import os
import openai
from tqdm import tqdm
from dotenv import load_dotenv
import json
import pandas as pd
import numpy as np
import ast
from collections import defaultdict
from typing import Set, List
import random

# Load your OpenAI API key from .env
openai.api_key = os.getenv("OPENAI_API_KEY")

# Configuration
INPUT_DIR = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed"
PREV_FILTER = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/sanityFiltered_s4.xlsx"
EMBEDDINGS = ""
EMBEDDING_MODEL = "text-embedding-3-small"
embeddingResults = {
    "filename": [],
    "embedding": []
}

bound = 0.85

def get_files():
    df = pd.read_excel(PREV_FILTER, sheet_name="Sheet1")
    prevFilter = df.to_dict(orient="list")

    filenames = [] 
    for i in range(len(prevFilter["filename"])):
        if prevFilter["keepTrash"][i] == "KEEP":
            filenames.append(os.path.join(INPUT_DIR, prevFilter["filename"][i]))
    
    return filenames

def read_file(filepath):
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            return f.read()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return ""

def get_embedding(text, model=EMBEDDING_MODEL):
    try:
        response = openai.embeddings.create(
            model=model,
            input=text
        )
        return response.data[0].embedding
    except Exception as e:
        print(f"Error generating embedding: {e}")
        return None

def embed_dafny_directory():
    files = get_files()

    for path in tqdm(files, desc="Embedding Dafny files"):
        content = read_file(path)
        if not content:
            continue

        embedding = get_embedding(content)
        if embedding:
            embeddingResults["filename"].append(os.path.basename(path))
            embeddingResults["embedding"].append(embedding)
            if len(embedding) != 1536:
                print(os.path.basename(path) + "embedding is the incorrect length")

    output_path = '/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/embeddings.json'
    with open(output_path, "w") as f:
        json.dump(embeddingResults, f, indent=2)
    
def pairwise_all():
    with open( '/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/embeddings.json', "r") as f:
        embeddingResults = json.load(f)

    allPairs = []

    for i in range(len(embeddingResults["filename"])):
        allPairs.append([])
        for j in range(i):
            embed1 = embeddingResults["embedding"][i]
            embed2 = embeddingResults["embedding"][j]
            allPairs[i].append(cosine_similarity(embed1, embed2))
    
    format_results(allPairs, embeddingResults["filename"])

    # Save with filenames and matrix
    result = {
        "filenames": embeddingResults["filename"],
        "similarity_matrix": allPairs
    }

    with open("pairwise_cosine.json", "w") as f:
        json.dump(result, f, indent=2)

def cosine_similarity(embed1, embed2):
    embed1 = np.array(embed1)
    embed2 = np.array(embed2)
    
    dot_product = np.dot(embed1, embed2)
    norm1 = np.linalg.norm(embed1)
    norm2 = np.linalg.norm(embed2)
    
    if norm1 == 0 or norm2 == 0:
        return 0.0  # Avoid division by zero
    
    return dot_product / (norm1 * norm2)

def format_results(matrix, filenames):
    formatted = dict()

    for i in range(len(filenames)):
        formatted[filenames[i]] = matrix[i]  + [None] * (len(matrix[-1]) - len(matrix[i]))
    
    df_result = pd.DataFrame(formatted)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/duplicate_check_s5'
    '.xlsx', index=False)

def identify_duplicates(minVal):
    with open('pairwise_cosine.json', "r") as f:
        rawDuplicates = json.load(f)

    duplicates = [] 

    for i in range(len(rawDuplicates["filenames"])):
        for j in range(i):
            if rawDuplicates["similarity_matrix"][i][j] >= minVal: 
                duplicates.append((rawDuplicates["filenames"][i], rawDuplicates["filenames"][j]))
    
    # print(duplicates)
    print(len(duplicates))
    with open("duplicate_pairs{minVal}.json", "w") as f:
        json.dump(duplicates, f, indent=2)

    return duplicates

def build_graph(edges):
    graph = defaultdict(set)
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    return graph

def bron_kerbosch(R: Set[str], P: Set[str], X: Set[str], graph, cliques: List[Set[str]]):
    if not P and not X:
        cliques.append(R)
        return
    for v in list(P):
        bron_kerbosch(R | {v}, P & graph[v], X & graph[v], graph, cliques)
        P.remove(v)
        X.add(v)

def find_maximal_cliques(edges):
    graph = build_graph(edges)
    all_nodes = set(graph.keys())
    cliques = []
    bron_kerbosch(set(), all_nodes, set(), graph, cliques)
    return cliques

def format_components(components):
    formatted = dict()
    for i in range(len(components)):
        formatted[i] = []
        for a in components[i]:
            formatted[i].append(a)
    
    max_len = max(len(lst) for lst in formatted.values())

    # Step 3: Pad all lists to the same length
    for i in formatted:
        formatted[i] += [None] * (max_len - len(formatted[i]))  # or use "" if you prefer

    df_result = pd.DataFrame(formatted)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/duplicate_check_2_0.75_s5'
    '.xlsx', index=False)

def delete_duplicates(duplicates):
    delete = []
    kept = []
    for i in range(len(duplicates)):
        cur = list(duplicates[i])
        save = random.randint(0, len(cur)-1)
        i = 0
        while cur[save] in kept and i < 10:
            save = random.randint(0, len(cur)-1)
            i += 1 
        kept.append(cur[save])

        for i in range(len(cur)):
            if i != save and cur[i] not in delete:
                delete.append(cur[i])
    
    print("delete length:")
    print(len(delete))

    df = pd.read_excel(PREV_FILTER, sheet_name="Sheet1")
    prevFilter = df.to_dict(orient="list")
    
    newFilter = {
        "index": [],
        "filename": [],
        "fileid": [],
        "reasoning": [],
    }

    for i in range(len(prevFilter["filename"])):
        if prevFilter["filename"][i] not in delete:
            newFilter["index"].append(prevFilter["index"][i])
            newFilter["filename"].append(prevFilter["filename"][i])
            newFilter["fileid"].append(prevFilter["fileid"][i])
            newFilter["reasoning"].append(prevFilter["reasoning"][i])

    df_result = pd.DataFrame(newFilter)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/duplicate_filter_s5'
    '.xlsx', index=False)

    return newFilter 


if __name__ == "__main__":
    # embed_dafny_directory()
    # pairwise_all()
    edges = identify_duplicates(0.75)
    connected = find_maximal_cliques(edges)
    print("connected length is:")
    print(len(connected))
    # format_components(connected)
    delete_duplicates(connected)