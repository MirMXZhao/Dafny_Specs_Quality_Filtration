import os 
import pandas as pd
from DafnyBench.filtration_ai.steps.formatted_prompts import prompts
import anthropic
import json
import time
from concurrent.futures import ThreadPoolExecutor
import threading

ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)

def intermediate_filter(data):
    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/filterProblems.xlsx", sheet_name="Sheet1")
    prevFilter = df.to_dict(orient="list")

    prevKeep = [] 

    for i in range(len(prevFilter["filename"])):
        if prevFilter["keepTrash"][i] == "KEEP":
            prevKeep.append(data["id"].index(prevFilter["fileid"][i]))
    return prevKeep

def filter_problem_concurrent(data, prompts, filtered, maxTokens=100, sheetName = 'sheet2', max_workers=10):
    """Concurrent processing alternative"""
    
    def process_single_file(i):
        filename = data["filename"][i]
        fileid = data["id"][i]
        
        try:
            response = client.beta.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens=maxTokens,
                system=[
                    {
                        "type": "text",
                        "text": prompts["filter_problems"]["overall_goal"] + prompts["filter_problems"]["task"],
                        "cache_control": {"type": "ephemeral"}
                    }
                ],
                messages=[
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "text",
                                "text": prompts["filter_problems"]["output_request"] + prompts["filter_problems"]["file"],
                                "cache_control": {"type": "ephemeral"}
                            },
                            {
                                "type": "document",
                                "source": {
                                    "type": "file",
                                    "file_id": fileid
                                }
                            }
                        ]
                    }
                ],
                betas=["files-api-2025-04-14"],
            )
            
            text = response.content[0].text
            keep_trash, violated, reasoning = text.splitlines()
            
            # Print progress for first 10 and every 50
            if i < 5 or i % 50 == 0:
                print(f"Completed {i}: {filename}")
                print(f"  Keep/Trash: {keep_trash}")
                print(f"  Violated: {violated}")
                print(f"  Reasoning: {reasoning}")
            
            return (i, filename, fileid, keep_trash, violated, reasoning)
        
        except Exception as e:
            print(f"Error processing {filename}: {str(e)}")
            return (filename, fileid, f"ERROR: {str(e)}", "ERROR", "ERROR")
    
    # Process files concurrently
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(process_single_file, i) for i in filtered]
        
        result = {
            "index": [],
            "filename": [],
            "fileid": [],
            "keepTrash": [],
            "violated": [],
            "reasoning": []
        }
        
        for future in futures:
            i, filename, fileid, keep_trash, violated, reasoning = future.result()
            result["index"].append(i)
            result["filename"].append(filename)
            result["fileid"].append(fileid)
            result["keepTrash"].append(keep_trash)
            result["violated"].append(violated)
            result["reasoning"].append(reasoning)
    
    # Save results
    df_result = pd.DataFrame(result)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/filterProblems2.xlsx', sheet_name=sheetName, index=False)
    
    print(f"Processing complete! Results saved to filterProblems.xlsx")
    return result

if __name__ == "__main__":
    print("Processing with concurrency")

    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/fileids.xlsx")
    data = df.to_dict(orient="list")
    filtered = intermediate_filter(data)
    print(len(filtered))
    result = filter_problem_concurrent(data, prompts, filtered, maxTokens=100, sheetName = 'Sheet1', max_workers=15)


