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

renamed_files = {
    "old_name": [],
    "new_name": [],
}

def intermediate_filter(data):
    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/duplicate_filter_s5.xlsx", sheet_name="Sheet1")
    prevFilter = df.to_dict(orient="list")

    prevKeep = [] 

    for i in range(len(prevFilter["filename"])):
        prevKeep.append(data["id"].index(prevFilter["fileid"][i]))
    return prevKeep

def tests_problem_concurrent(data, prompts, filtered, maxTokens=100, sheetName = 'sheet2', max_workers=10):
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
                        "text": prompts["write_tests"]["overall_goal"] + prompts["write_tests"]["examples"],
                        "cache_control": {"type": "ephemeral"}
                    }
                ],
                messages=[
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "text",
                                "text": prompts["write_tests"]["output_request"] + prompts["write_tests"]["file"],
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
            
            test = response.content[0].text
            
            # Print progress for first 10 and every 50
            if i < 20 or i % 50 == 0:
                print(f"Completed {i}: {filename}")
                print(f"Test: {test}")
                print(response)
            
            return (i, filename, fileid, test)
        
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
            "test": [], 
        }
        
        for future in futures:
            i, filename, fileid, test = future.result()
            result["index"].append(i)
            result["filename"].append(filename)
            result["fileid"].append(fileid)
            result["test"].append(test)
            new_file(filename, test)
    
    # Save results
    df_result = pd.DataFrame(result)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/tests_s6.xlsx', sheet_name=sheetName, index=False)
    
    print(f"Processing complete! Results saved to tests_s6.xlsx")
    return result

def new_file(filename, tests):
    # Read original file
    old_directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed"
    file_path = os.path.join(old_directory, filename)

    with open(file_path, 'r') as f:
        original_content = f.read()
    
    new_name = str(len(renamed_files["old_name"]) + 1) + "_" + filename

    renamed_files["old_name"].append(filename)
    renamed_files["new_name"].append(new_name)

    # Combine with tests
    new_content = original_content + '\n\n' + tests.strip() + '\n'
    
    # Write to new file
    new_directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/filtered_and_tests" 

    full_path = os.path.join(new_directory, new_name)
    with open(full_path, 'w') as f:
        f.write(new_content)

if __name__ == "__main__":
    print("Processing with concurrency")

    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/fileids.xlsx")
    data = df.to_dict(orient="list")
    filtered = intermediate_filter(data)
    print(len(filtered))
    result = tests_problem_concurrent(data, prompts, filtered, maxTokens=2000, sheetName = 'Sheet1', max_workers=10)

    df_result = pd.DataFrame(renamed_files)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/renaming.xlsx', index=False)
    

