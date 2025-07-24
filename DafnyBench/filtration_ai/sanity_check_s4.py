import os 
import pandas as pd
from formatted_prompts import prompts
import anthropic
import json
import time
from concurrent.futures import ThreadPoolExecutor
import threading

data = {
    "file_label": [],
    "file_name": [],
    "num_methods": [],
    "num_lemmas": [],
    "num_classes": [],
    "num_functions": [],
    "num_predicates": [],
    "num_ensures": [],
    "num_requires": [],
    "num_lines": [],
    "num_no_ensures": [],
    "num_no_requires": [],
    "num_none_either": [],
}

def intermediate_filter():
    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/filterProblems2.xlsx", sheet_name="Sheet1")
    prevFilter = df.to_dict(orient="list")

    prevKeep = [] 

    for i in range(len(prevFilter["filename"])):
        if prevFilter["keepTrash"][i] == "KEEP":
            prevKeep.append(prevFilter["filename"][i])
    return prevKeep

def extract(prevKeep):
    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/output.xlsx", sheet_name="Sheet1")
    prevData = df.to_dict(orient="list")

    for i in range(len(prevData["file_name"])):
        print(prevData["file_name"][i])
        if prevData["file_name"][i] in prevKeep:
            data["file_label"].append(prevData["file_label"][i])
            data["file_name"].append(prevData["file_name"][i])
            data["num_methods"].append(prevData["num_methods"][i])
            data["num_lemmas"].append(prevData["num_lemmas"][i])
            data["num_classes"].append(prevData["num_classes"][i])
            data["num_functions"].append(prevData["num_functions"][i])
            data["num_predicates"].append(prevData["num_predicates"][i])
            data["num_ensures"].append(prevData["num_ensures"][i])
            data["num_requires"].append(prevData["num_requires"][i])
            data["num_lines"].append(prevData["num_lines"][i])
            data["num_no_ensures"].append(prevData["num_ensures"][i])
            data["num_no_requires"].append(prevData["num_requires"][i])
            data["num_none_either"].append(prevData["num_none_either"][i])
        
    df_result = pd.DataFrame(data)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/sanityCheck.xlsx', index=False)

if __name__ == "__main__":
    kept = intermediate_filter()

    extract(kept)
    