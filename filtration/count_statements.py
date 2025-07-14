import pandas as pd 
import os
import re
import heapq

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
def find_noncommented_statement_indices(text, word):
    indices = []
    current_index = 0
    phrase = r'\b' + re.escape(word) + r'\b' 

    for line in text.splitlines(keepends=True):  # keep line breaks to track accurate indices
        # Remove comments
        code = line.split('//')[0]

        # Use regex to find whole-word "method"
        for match in re.finditer(phrase, code):
            indices.append(current_index + match.start())

        # Move current_index forward
        current_index += len(line)

    return indices

def num_methods_ensures(text):
    methods = find_noncommented_statement_indices(content, "method")
    lemmas = find_noncommented_statement_indices(content, "lemma")
    functions = find_noncommented_statement_indices(content, "function")
    predicates = find_noncommented_statement_indices(content, "predicate")
    data["num_methods"].append(len(methods))
    data["num_lemmas"].append(len(lemmas))
    data["num_functions"].append(len(functions))
    data["num_predicates"].append(len(predicates))

    merged = list(heapq.merge(methods, lemmas, functions))

    ensures = find_noncommented_statement_indices(content, "ensures")
    requires = find_noncommented_statement_indices(content, "requires")
    data["num_ensures"].append(len(ensures))
    data["num_requires"].append(len(requires))

    data["num_no_ensures"].append(0)
    data["num_no_requires"].append(0)
    data["num_none_either"].append(0)

    e_idx = 0
    r_idx = 0
    for i in range(len(merged)-1):
        while e_idx < len(ensures) and ensures[e_idx] < merged[i]:
            e_idx +=1 
        while r_idx < len(requires) and requires[r_idx] < merged[i]:
            r_idx +=1 
        if (e_idx >= len(ensures) or ensures[e_idx] > merged[i+1]) and (r_idx >= len(requires) or requires[r_idx] > merged[i+1]):
            data["num_none_either"][-1] += 1
        else:
            if e_idx >= len(ensures) or ensures[e_idx] > merged[i+1]:
                data["num_no_ensures"][-1] += 1
            if r_idx >= len(requires) or requires[r_idx] > merged[i+1]:
                data["num_no_requires"][-1] += 1
    if len(merged) > 0:
        if (len(ensures) == 0 or ensures[-1] < merged[-1]) and (len(requires) == 0 or requires[-1] < merged[-1]):
            data["num_none_either"][-1] += 1
        else:
            if (len(ensures) == 0 or ensures[-1] < merged[-1]):
                data["num_no_ensures"][-1] += 1
            if (len(requires) == 0 or requires[-1] < merged[-1]):
                data["num_no_requires"][-1] += 1
        
    



if __name__ == "__main__":
    directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed"
    num_files = 0 
    for filename in os.listdir(directory):
        num_files +=1
        data["file_name"].append(filename)
        data["file_label"].append(num_files)
        file_path = os.path.join(directory, filename)
        if os.path.isfile(file_path):
            with open(file_path, 'r') as f:
                content = f.read()
                data["num_classes"].append(len(find_noncommented_statement_indices(content, "class")))
                data["num_lines"].append(content.count('\n') + 1)
                num_methods_ensures(content)
    
    df = pd.DataFrame(data)
    # To export to an Excel file
    df.to_excel('output.xlsx', sheet_name='Sheet1', index=False)



    