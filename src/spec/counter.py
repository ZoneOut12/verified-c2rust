from extract import ACSLType, ACSLJudger
from transform import TransformError
from tree_sitter import Language, Parser
from ACSLLexer import ACSLLexer
from ACSLParser import ACSLParser
from antlr4 import InputStream, CommonTokenStream
import re


class RawPointerCounter:
    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.raw_pointer_files = []
        pass

    def get_raw_pointer_files(self):
        return self.raw_pointer_files

    def print_node(self, node):
        print(
            f"Node type: {node.type}, Text: {node.text.decode('utf-8')}, Children: {len(node.children)}"
        )
        for child in node.children:
            self.print_node(child)

    def contains_raw_pointer(self, file_path: str) -> bool:
        """
        Check if the file contains raw pointers.
        Args:
            file_path (str): The path to the file.
        Returns:
            bool: True if the file contains raw pointers, False otherwise.
        """
        with open(file_path, "r", encoding="utf-8") as file:
            code = file.read()
        tree = self.parser.parse(code.encode("utf-8"))
        root_node = tree.root_node
        if self.detect_node_has_raw_pointer(root_node):
            self.raw_pointer_files.append(file_path)
            return True
        else:
            return False

    def detect_node_has_raw_pointer(self, node):
        if node.type == "pointer_declarator":
            return True
        for child in node.children:
            if self.detect_node_has_raw_pointer(child):
                return True
        return False


class TransformErrorCounter:
    def __init__(self):
        self.counts = {
            "At": 0,
            "InductiveDef": 0,
            "AxiomaticDecl": 0,
            "UnsupportedType": 0,
            "ReadsClause": 0,
            "TerminatesClause": 0,
            "ParamIsPointerType": 0,
            "GhostCode": 0,
            "Labels": 0,
            "Others": 0,
        }

    def copy(self):
        new_counter = TransformErrorCounter()
        new_counter.counts = self.counts.copy()
        return new_counter

    def items(self):
        return self.counts.items()

    def get(self, key, default=None):
        return self.counts.get(key, default)

    def __getitem__(self, key):
        return self.counts[key]

    def __setitem__(self, key, value):
        self.counts[key] = value

    def update(self, error: TransformError):
        if error == TransformError.At:
            self.counts["At"] += 1
        elif error == TransformError.InductiveDef:
            self.counts["InductiveDef"] += 1
        elif error == TransformError.AxiomaticDecl:
            self.counts["AxiomaticDecl"] += 1
        elif error == TransformError.UnsupportedType:
            self.counts["UnsupportedType"] += 1
        elif error == TransformError.ReadsClause:
            self.counts["ReadsClause"] += 1
        elif error == TransformError.TerminatesClause:
            self.counts["TerminatesClause"] += 1
        elif error == TransformError.ParamIsPointerType:
            self.counts["ParamIsPointerType"] += 1
        elif error == TransformError.Labels:
            self.counts["Labels"] += 1
        elif error == TransformError.GhostCode:
            self.counts["GhostCode"] += 1
        else:
            self.counts["Others"] += 1

    def get_counts(self):
        return self.counts


class ACSLTypeCounter:
    judger = ACSLJudger()

    def __init__(self, lang_lib):
        self.LANGUAGE_LIB = lang_lib
        self.LANGUAGE = Language(self.LANGUAGE_LIB, "c")
        self.parser = Parser()
        self.parser.set_language(self.LANGUAGE)
        self.counts = {
            "funcContract": 0,
            "loop": 0,
            "assertion": 0,
            "ghostCode": 0,
            "logicConstDef": 0,
            "logicFunctionDef": 0,
            "logicPredicateDef": 0,
            "lemmaDef": 0,
            "inductiveDef": 0,
            "axiomaticDecl": 0,
            "others": 0,
        }

    def remove_non_acsl_comments(self, file_path):
        with open(file_path, "r", encoding="utf-8") as file:
            code = file.read()
        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)
        return code

    def extract_acsl_comments(self, code: str) -> list:
        tree = self.parser.parse(code.encode("utf-8"))
        root_node = tree.root_node

        acsl_comments = []

        def traverse(node):
            if node.type == "comment":
                text = code[node.start_byte : node.end_byte]
                acsl_comments.append(text)
            for child in node.children:
                traverse(child)

        traverse(root_node)
        return acsl_comments

    def count_acsl_types(self, annotations):

        for annot in annotations:
            input_stream = InputStream(annot)
            lexer = ACSLLexer(input_stream)
            token_stream = CommonTokenStream(lexer)
            parser = ACSLParser(token_stream)
            tree = parser.acsl()

            result = self.judger.visitAcsl(tree)
            if result.type == ACSLType.GHOSTCODE:
                self.counts["ghostCode"] += 1
            elif result.type == ACSLType.ASSERTION:
                self.counts["assertion"] += 1
            elif result.type == ACSLType.LOOP:
                self.counts["loop"] += 1
            elif result.type == ACSLType.CONTRACT:
                self.counts["funcContract"] += 1
            elif result.type == ACSLType.LOGICDEF:
                for key, value in result.counts.items():
                    self.counts[key] += value
            else:
                self.counts["others"] += 1

    def pipeline(self, file_path):
        cleaned_code = self.remove_non_acsl_comments(file_path=file_path)
        acsl_comments = self.extract_acsl_comments(code=cleaned_code)
        self.count_acsl_types(acsl_comments)

    def getTypeCounts(self):
        return self.counts


if __name__ == "__main__":
    pass
