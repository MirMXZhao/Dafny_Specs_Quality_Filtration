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
from Concurrency import Concurrency

class DuplicateFinder():
    def __init__(self, filepaths: List[str], input_file:str, output_file: str, concurrency: Concurrency, bound: float = 0.85):
        self.concurrency = concurrency
        self.filepaths = filepaths
        self.bound = bound
        self.output_dir = "./filtration_pipeline/results"
        self.input_filepath = os.path.join(self.output_dir, input_file)
        self.output_filepath = os.path.join(self.output_dir, output_file) 
        self.embedding_results = {
            "filename": [],
            "embedding": []
        }
        self.similarity_matrix = []
        self.duplicates = []
        self.final_result = []
        
    def get_embedding(self) -> List[float]:
        """
        Get embeddings for all files in the filepaths list.
        This method uses the Concurrency class to embed files concurrently.
        results stored in embedding_results. 
        """
        self.embedding_results["filename"] = [os.path.basename(filepath) for filepath in self.filepaths]
        self.embedding_results["embedding"] = self.concurrency.embed_files(self.filepaths)
        output_path = os.path.join(self.output_dir, "embeddings.json")
        with open(output_path, "w") as f:
            json.dump(self.embedding_results, f, indent=2)
    
    def pairwise_all(self):
        """
        Compute pairwise cosine similarity for all embeddings.
        """
        if len(self.embedding_results["filename"]) == 0:
            with open( os.path.join(self.output_dir, "embeddings.json"), "r") as f:
                self.embedding_results = json.load(f)

        allPairs = []

        for i in range(len(self.embedding_results["filename"])):
            allPairs.append([])
            for j in range(i):
                embed1 = self.embedding_results["embedding"][i]
                embed2 = self.embedding_results["embedding"][j]
                allPairs[i].append(self.cosine_similarity(embed1, embed2))
        
        self.similarity_matrix = allPairs

        # Save with filenames and matrix
        result = {
            "filenames": self.embedding_results["filename"],
            "similarity_matrix": allPairs
        }

        with open("pairwise_cosine.json", "w") as f:
            json.dump(result, f, indent=2)

    def cosine_similarity(self, embed1, embed2):
        """
        Compute the cosine similarity between two embeddings. 
        Returns a float value between -1 and 1.
        """
        embed1 = np.array(embed1)
        embed2 = np.array(embed2)
        
        dot_product = np.dot(embed1, embed2)
        norm1 = np.linalg.norm(embed1)
        norm2 = np.linalg.norm(embed2)
        
        if norm1 == 0 or norm2 == 0:
            return 0.0  # Avoid division by zero
        
        return dot_product / (norm1 * norm2)
    
    def format_results(self, matrix, filenames):
        """
        reformats similarity matrix to be enterable into a spreadsheet
        """
        formatted = dict()

        for i in range(len(filenames)):
            formatted[filenames[i]] = matrix[i]  + [None] * (len(matrix[-1]) - len(matrix[i]))
        
        return formatted
    
    def identify_duplicates(self):
        """
        Identify duplicates based on the similarity matrix.
        Returns a list of tuples where each tuple contains the filenames of the duplicates.
        """
        duplicates = [] 
        for i in range(len(self.similarity_matrix)):
            for j in range(len(self.similarity_matrix[i])):
                if self.similarity_matrix[i][j] >= self.bound: 
                    duplicates.append((self.embedding_results["filename"][i], self.embedding_results["filename"][j]))

        self.duplicates = duplicates
        return duplicates

    def build_graph(self, edges):
        """
        Build a graph from the list of edges.
        Each edge is a tuple of two filenames.
        Returns a dictionary where keys are filenames and values are sets of connected filenames.
        """
        graph = defaultdict(set)
        for u, v in edges:
            graph[u].add(v)
            graph[v].add(u)
        return graph

    def bron_kerbosch(self, R: Set[str], P: Set[str], X: Set[str], graph, cliques: List[Set[str]]):
        if not P and not X:
            cliques.append(R)
            return
        for v in list(P):
            self.bron_kerbosch(R | {v}, P & graph[v], X & graph[v], graph, cliques)
            P.remove(v)
            X.add(v)

    def find_maximal_cliques(self):
        graph = self.build_graph(self.duplicates)
        all_nodes = set(graph.keys())
        cliques = []
        self.bron_kerbosch(set(), all_nodes, set(), graph, cliques)
        return cliques

    def delete_duplicates(self, cliques):
        delete = []
        kept = []
        for i in range(len(cliques)):
            cur = list(cliques[i])
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

        df = pd.read_excel(self.input_filepath, sheet_name="Sheet1")
        prev_filter = df.to_dict(orient="list")
        
        newFilter = {
            "filename": [],
            "filepath":[],
            "keepToss":[],
            "duplicateGroup": [],
        }

        for i in range(len(prev_filter["filename"])):
            newFilter["filename"].append(prev_filter["filename"][i])
            newFilter["filepath"].append(prev_filter["filepath"][i])
            if prev_filter["filename"][i] not in delete:
                newFilter["keepToss"].append("KEEP")
                newFilter["duplicateGroup"].append("")
            else:
                newFilter["keepToss"].append("TOSS")
                group_number = next((j for j, group in enumerate(self.duplicates) if prev_filter["filename"][i] in group), None)
                newFilter["duplicateGroup"].append(str(group_number) if group_number is not None else "")

        return newFilter 
    
    def run(self):
        # Step 1: Get embeddings
        # self.get_embedding()
        # print("Embeddings obtained")

        # Step 2: Compute pairwise cosine similarity
        self.pairwise_all()
        print("Pairwise cosine similarity computed")

        # Step 3: Identify duplicates based on the similarity matrix
        self.identify_duplicates()
        print("Duplicates identified")

        cliques = self.find_maximal_cliques()
        print("Maximal cliques found")

        # Step 6: Delete duplicates and save the final result
        final_result = self.delete_duplicates(cliques)
        print("Duplicates deleted and final result prepared")

        df1 = pd.DataFrame(final_result)
        formatted_similarities = self.format_results(self.similarity_matrix, self.embedding_results["filename"])
        df2 = pd.DataFrame(formatted_similarities)

        # Write both to the same Excel file
        with pd.ExcelWriter(self.output_filepath, engine='openpyxl') as writer:
            df1.to_excel(writer, sheet_name="Sheet1", index=False)
            df2.to_excel(writer, sheet_name="Sheet2", index=False)
        
        return final_result