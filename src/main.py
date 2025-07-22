from utils import AttrDict
import json, subprocess, argparse, sys, os, tempfile, shutil

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run the migration framework.")
    parser.add_argument(
        "-m",
        "--mode",
        type=str,
        choices=["cached", "local", "api"],
        default="cached",
        help="C-to-Rust translation mode: 'cached' (use pre-translated files), 'local' (use local LLM), or 'api' (call LLM via API)",
    )

    DEFAULT_TRANSLATED_DIR = os.path.abspath("../transpiled_rust")

    # Mode-specific arguments
    parser.add_argument(
        "-p",
        "--local_llm_path",
        type=str,
        help="Path to local LLM model (used in 'local' mode)",
    )
    parser.add_argument(
        "-k",
        "--api_key",
        type=str,
        help="API key for calling LLM service (used in 'api' mode)",
    )
    parser.add_argument("-l", "--model", type=str, help="Model name for the OpenAI API")
    parser.add_argument(
        "-b",
        "--base_url",
        type=str,
        default=None,
        help="Optional base URL for the LLM API (e.g., for non-OpenAI endpoints)",
    )

    parser.add_argument(
        "--type-guidance",
        choices=["true", "false"],
        default="true",
        help="Enable or disable type guidance (true or false), default is true",
    )

    args = parser.parse_args()

    if args.mode == "cached":
        print(f"Using saved translations located at: {DEFAULT_TRANSLATED_DIR}")

    elif args.mode == "local":
        if not args.local_llm_path:
            parser.error("In 'local' mode, you must provide --local_llm_path")
        print(f"Using local LLM model at: {args.local_llm_path}")

    elif args.mode == "api":
        if not args.api_key:
            parser.error("In 'api' mode, you must provide --api_key")
        if not args.model:
            parser.error("In 'api' mode, you must provide --model")
        print(f"Using API-based LLM: {args.model}")

    mode = args.mode if args.mode else "cached"
    local_llm_path = args.local_llm_path if args.local_llm_path else None
    api_key = args.api_key if args.api_key else None
    api_model = args.model if args.model else None
    base_url = args.base_url if args.base_url else None

    parent_dir = os.path.abspath(os.path.join(os.getcwd(), ".."))
    temp_dir = tempfile.mkdtemp(dir=parent_dir)
    input_c = os.path.join(temp_dir, "input.c")
    result_rs = os.path.join(temp_dir, "result.rs")
    source_c = os.path.join(temp_dir, "source.c")
    src_dir = os.path.join(temp_dir, "src")
    os.makedirs(src_dir, exist_ok=True)
    refactored_rs = os.path.join(src_dir, "refactored_source.rs")
    source_rs = os.path.join(src_dir, "source.rs")

    for path in [input_c, result_rs, source_c, refactored_rs, source_rs]:
        with open(path, "w", encoding="utf-8") as f:
            f.write(f"\n")

    temp_dir_path = os.path.abspath(temp_dir)

    json_file_path = r"./config.json"
    data = {}
    with open(json_file_path, "r", encoding="utf-8") as file:
        data = json.load(file)
    config = AttrDict(data)
    result = subprocess.run(
        [
            "python",
            "./spec/pipeline.py",
            config.dataset_txt,
            temp_dir_path,
            os.path.expanduser(config.verus),
            "./spec/build/my-languages.so",
            config.log_file,
            config.result_dir,
            config.repair_round_threshold,
            mode,
            local_llm_path if local_llm_path else "",
            api_key if api_key else "",
            api_model if api_model else "",
            base_url if base_url else "",
            config.temperature,
            config.max_tokens,
            config.top_p,
            DEFAULT_TRANSLATED_DIR,
            args.type_guidance,
        ],
        capture_output=True,
        text=True,
    )

    shutil.rmtree(temp_dir)
    print(result.stderr)
