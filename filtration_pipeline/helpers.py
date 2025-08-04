import os
import re
import yaml

def read_file(filepath):
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            return f.read()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return ""
    

def extract_dafny_code(llm_output: str) -> list[str]:
    """
    Extracts Dafny code blocks from LLM output.

    - If code blocks are found, returns them.
    - If none are found, assumes the entire output is Dafny code.

    Returns a list of Dafny code blocks as strings.
    """
    pattern = re.compile(r"```dafny\s+(.*?)```|```(?:\s*\n)?(.*?)```", re.DOTALL | re.IGNORECASE)
    matches = pattern.findall(llm_output)
    
    # Flatten tuples and filter empty strings
    code_blocks = [code for group in matches for code in group if code.strip()]

    if code_blocks:
        return [block.strip() for block in code_blocks]
    else:
        # No fenced blocks found — assume entire output is Dafny code
        return [llm_output.strip()]

def load_prompts(path="prompts.yaml"):
    script_dir = os.path.dirname(__file__)

    # Join it with the config filename
    config_path = os.path.join(script_dir, path)

    with open(config_path, "r") as f:
        data = yaml.safe_load(f)
    
    return data