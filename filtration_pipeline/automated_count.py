import pandas as pd 
import os
import re
import heapq

def find_noncommented_statement_indices(text, word):
    indices = []
    current_index = 0
    phrase = r'\b' + re.escape(word) + r'\b'

    in_block_comment = False

    for line in text.splitlines(keepends=True):  # preserve line breaks
        code = ''
        i = 0
        while i < len(line):
            if in_block_comment:
                end = line.find('*/', i)
                if end == -1:
                    # Still inside block comment
                    i = len(line)
                else:
                    in_block_comment = False
                    i = end + 2
            elif line.startswith('//', i):
                # Line comment starts, skip the rest of the line
                break
            elif line.startswith('/*', i):
                in_block_comment = True
                i += 2
            else:
                code += line[i]
                i += 1

        # Find matches in code portion only
        for match in re.finditer(phrase, code):
            indices.append(current_index + match.start())

        current_index += len(line)

    return indices

def num_methods_ensures(content):
    data = {}
    methods = find_noncommented_statement_indices(content, "method")
    lemmas = find_noncommented_statement_indices(content, "lemma")
    functions = find_noncommented_statement_indices(content, "function")
    predicates = find_noncommented_statement_indices(content, "predicate")
    data["num_methods"] = len(methods)
    data["num_lemmas"] = len(lemmas)
    data["num_functions"] = len(functions)
    data["num_predicates"] = len(predicates)

    merged = list(heapq.merge(methods, lemmas, functions))

    ensures = find_noncommented_statement_indices(content, "ensures")
    requires = find_noncommented_statement_indices(content, "requires")
    data["num_ensures"] = len(ensures)
    data["num_requires"] = len(requires)

    data["num_no_ensures"] = 0
    data["num_no_requires"] = 0
    data["num_none_either"] = 0 

    e_idx = 0
    r_idx = 0
    for i in range(len(merged)-1):
        while e_idx < len(ensures) and ensures[e_idx] < merged[i]:
            e_idx +=1 
        while r_idx < len(requires) and requires[r_idx] < merged[i]:
            r_idx +=1 
        if (e_idx >= len(ensures) or ensures[e_idx] > merged[i+1]) and (r_idx >= len(requires) or requires[r_idx] > merged[i+1]):
            data["num_none_either"] += 1
        else:
            if e_idx >= len(ensures) or ensures[e_idx] > merged[i+1]:
                data["num_no_ensures"] += 1
            if r_idx >= len(requires) or requires[r_idx] > merged[i+1]:
                data["num_no_requires"] += 1
    if len(merged) > 0:
        if (len(ensures) == 0 or ensures[-1] < merged[-1]) and (len(requires) == 0 or requires[-1] < merged[-1]):
            data["num_none_either"] += 1
        else:
            if (len(ensures) == 0 or ensures[-1] < merged[-1]):
                data["num_no_ensures"] += 1
            if (len(requires) == 0 or requires[-1] < merged[-1]):
                data["num_no_requires"] += 1
    data["num_classes"] = len(find_noncommented_statement_indices(content, "class"))
    data["num_lines"] = content.count('\n') + 1
    
    return data
