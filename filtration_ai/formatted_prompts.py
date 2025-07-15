import yaml 
import os 

def load_prompts(path="prompts.yaml"):
    script_dir = os.path.dirname(__file__)

    # Join it with the config filename
    config_path = os.path.join(script_dir, "prompts.yaml")

    with open(config_path, "r") as f:
        data = yaml.safe_load(f)
    
    return data

prompts = load_prompts()
# print(prompts["check_bodies"]["task"])