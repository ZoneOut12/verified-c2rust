import os
import tempfile

cwd = os.getcwd()
script_dir = os.path.dirname(os.path.abspath(__file__))

from utils.tree_sitter_parse import TreeSitterParser, TypeClassifier, TypeKind
from analysis.lsp import RustAnalyzerClient
from spec.acslitem import NonTypedItemExtractor


class RustTypeAnalyzer:
    def __init__(self, lang_lib, logger=None):
        self.parser = TreeSitterParser(lang_lib, logger=logger)
        self.logger = logger
        self.lang_lib = lang_lib
        self.item_extractor = NonTypedItemExtractor(lang_lib=lang_lib, logger=logger)

    def printlog(self, *args, sep=" ", end="\n"):
        msg = sep.join(str(arg) for arg in args) + end
        if self.logger:
            self.logger.info(msg)
        else:
            print(*args, sep=sep, end=end)

    def insert_let_bindings(self, rust_code, line_num, items):
        """
        return: new_code, start_line, end_line
        """
        lines = rust_code.splitlines()

        insert_lines = [
            f"let verus_tmp{i + 1} = {item};" for i, item in enumerate(items)
        ]

        insert_at = line_num + 1
        lines[insert_at:insert_at] = insert_lines

        start_line = insert_at
        end_line = insert_at + len(items) - 1

        # concatenate the lines back into a single string
        new_code = "\n".join(lines)
        return new_code, start_line, end_line

    def find_function_brace_line(self, node, rust_code):
        if node.type == "function_item":
            for child in node.children:
                if child.type == "block":
                    start_byte = child.start_byte
                    brace_line = rust_code[:start_byte].count(b"\n") + 1
                    return brace_line
        for child in node.children:
            line = self.find_function_brace_line(child, rust_code)
            if line:
                return line
        return None

    def type_analysis(self, rust_file_path, acsl_info, target_project_dir):
        """
        rust_file_path: the path of the rust file
        acsl_info: the acsl info of the c file
        target_project_dir: the path of the project that contains the rust file
        return: the type of the non-typed items, and the corresponding index(the i-th acsl annotation in the file)
        e.g. [
            {"index":0,"item":"x","type":"i32"},
            {"index":1,"item":"y","type":"i32"},
            {"index":2,"item":"z","type":"i32"},
        ]
        """
        func_sigs = self.parser.rust_extract_function_signatures(
            rust_file_path=rust_file_path
        )
        self.parser.print_function_signatures(func_sigs)
        # for acsl in acsl_info["annotation"]:
        #     self.printlog(f"acsl: {acsl}")
        items = self.item_extractor.extract_non_typed_items(
            acsl_info=acsl_info, rust_file_path=rust_file_path
        )

        with open(rust_file_path, "r") as f:
            rust_code = f.read()

        typed_items = []
        type_classifier = TypeClassifier()

        for item in items:
            if not isinstance(item["position"], tuple):
                try:
                    typed_items.append(
                        {
                            "index": item["index"],
                            "func_name": item["position"],
                            "items": func_sigs[item["position"]],
                        }
                    )
                except Exception:
                    pass
                continue
            if len(item["items"]) == 0:
                continue
            rust_items_list = list(item["items"])
            insert_line = item["position"][0]
            new_code, start_line, end_line = self.insert_let_bindings(
                rust_code=rust_code, line_num=insert_line, items=rust_items_list
            )

            with tempfile.NamedTemporaryFile(
                suffix=".rs", mode="w+", delete=False
            ) as tmp:
                tmp.write(new_code)
                tmp_file_path = tmp.name
            # call rust-analyzer lsp client to get the type of the non-typed items
            lsp_client = RustAnalyzerClient(logger=self.logger)
            lsp_client.initialize(target_project_dir)
            lsp_client.copy_source_rs(tmp_file_path)
            lsp_client.did_open()
            resp = lsp_client.inlay_hint(start_line, 0, end_line + 1, 0)
            type_hints = lsp_client.extract_inlay_types(resp)

            for type_hint in type_hints:
                type_class = type_classifier.classify_type(type_hint[2])
                typed_items.append(
                    {
                        "index": item["index"],
                        "item": rust_items_list[int(type_hint[0]) - int(start_line)],
                        "type": type_class,
                    }
                )
            lsp_client.close()
            os.remove(tmp_file_path)

        return typed_items

    def is_typed_items_in_contract(typed_items):
        if "func_name" in typed_items.keys():
            return True
        return False

    def is_type_str_ref(type_kind):
        if type_kind == TypeKind.IMMUT_STR or type_kind == TypeKind.MUT_STR:
            return True
        return False

    def is_type_slice(type_kind):
        if (
            type_kind == TypeKind.MUT_SLICE
            or type_kind == TypeKind.IMMUT_SLICE
            or type_kind == TypeKind.IMMUT_STR
            or type_kind == TypeKind.MUT_STR
        ):
            return True
        return False

    def is_type_mut(type_kind):
        if (
            type_kind == TypeKind.MUT_VALUE
            or type_kind == TypeKind.MUT_SLICE
            or type_kind == TypeKind.MUT_STR
        ):
            return True
        return False

    def is_type_option(type_kind):
        if type_kind == TypeKind.OPTION:
            return True
        return False


if __name__ == "__main__":
    pass
