import subprocess, re


class Frama:
    def __init__(self):
        pass

    def verify(self, file_path):
        """
        Return True if frama-c -wp -wp-rte can verify `file_path` successfully.
        Return False if not.
        """

        proved_pattern = re.compile(r"Proved goals:\s+([0-9]+)\s*/\s*([0-9]+)")

        verified = False  # used to represent whether there is one solver can verify successfully

        for prover in ["z3", "cvc5"]:
            try:
                result = subprocess.run(
                    [
                        "frama-c",
                        "-wp",
                        "-wp-rte",
                        "-wp-timeout",
                        "5",
                        "-wp-prover",
                        prover,
                        file_path,
                    ],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    timeout=300,
                )
                output = result.stdout
            except subprocess.TimeoutExpired:
                continue
            except Exception as e:
                continue

            match = proved_pattern.search(output)
            if match:
                proved = int(match.group(1))
                total = int(match.group(2))
                if proved == total:
                    # print(f"  All goals proved with {prover}")
                    verified = True
                    break
                else:
                    # print(f"  Partial proof with {prover}: {proved}/{total}")
                    pass
            else:
                # print(f"  No 'Proved goals' found with {prover}")
                pass

        if not verified:
            # print(f"Verification failed for {file_path} with all provers.")
            return False
        return True
