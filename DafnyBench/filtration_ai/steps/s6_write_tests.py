import os 
import pandas as pd
from formatted_prompts import prompts
import anthropic
import json
import time
from concurrent.futures import ThreadPoolExecutor
import threading

ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)

def tests_problem_concurrent(files, prompts, maxTokens=1000, sheetName = 'sheet2', max_workers=10):
    """Concurrent processing alternative"""

    def write_tests_iterative(i, tests):
        filepath = files[i]
        filename = os.path.basename(filepath)
        with open(filepath, 'r', encoding='utf-8') as f:
            fileContent = f.read()

        try:
            response = client.beta.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens= maxTokens,
                system=[
                    {
                        "type": "text",
                        "text": prompts["iterative_tests"]["overall_goal"],
                        "cache_control": {"type": "ephemeral"}
                    }
                ],
                messages=[
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "text",
                                "text": prompts["iterative_tests"]["output_request"] + prompts["iterative_tests"]["file"] + fileContent,
                                "cache_control": {"type": "ephemeral"}
                            },
                            {
                                "type": "text",
                                "text": prompts["iterative_tests"]["tests"] + tests,
                            }
                            
                        ]
                    }
                ],
                betas=["files-api-2025-04-14"],
            )
            
            newTest = response.content[0].text

            return (newTest, len(newTest) < 10)
            # if len(newTest) > 10:
            #     final_test = tests + "\n" + newTest 
            
            # return (final_test, len(newTest) < 10)
        
        except Exception as e:
            print(f"Error processing {filename}: {str(e)}")
            return (filename, f"ERROR: {str(e)}", "ERROR", "ERROR")
        
    
    def process_single_file(i):
        filepath = files[i]
        filename = os.path.basename(filepath)
        with open(filepath, 'r', encoding='utf-8') as f:
            fileContent = f.read()
        
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
                                "text": prompts["write_tests"]["output_request"] + prompts["write_tests"]["file"] + fileContent,
                                "cache_control": {"type": "ephemeral"}
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

            ctr = 0; 
            cont = False
            while (ctr < 1 and not cont):
                test, cont = write_tests_iterative(i, test)
                ctr += 1
            
            return (i, filename, test)
        
        except Exception as e:
            print(f"Error processing {filename}: {str(e)}")
            return (filename, f"ERROR: {str(e)}", "ERROR", "ERROR")
    
    # Process files concurrently
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(process_single_file, i) for i in range(len(files))] 
        
        result = {
            "index": [],
            "filename": [],
            "test": [], 
        }
        
        for future in futures:
            i, filename, test = future.result()
            result["index"].append(i)
            result["filename"].append(filename)
            result["test"].append(test)
            new_file(filename, test)
    
    # Save results
    df_result = pd.DataFrame(result)
    df_result.to_excel('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/tests_s6.xlsx', sheet_name=sheetName, index=False)
    
    print(f"Processing complete! Results saved to tests_s6.xlsx")
    return result

def new_file(filename, tests):
    # Read original file
    old_directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/filtered"
    file_path = os.path.join(old_directory, filename)

    with open(file_path, 'r') as f:
        original_content = f.read()
    
    # Combine with tests
    new_content = original_content + '\n\n////////TESTS////////\n\n' + tests.strip() + '\n'
    
    # Write to new file
    new_directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/tests" 

    full_path = os.path.join(new_directory, filename)
    with open(full_path, 'w') as f:
        f.write(new_content)

if __name__ == "__main__":
    print("Processing with concurrency")
    directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/filtered"
    allFiles = []
    for filename in os.listdir(directory):
        file_path = os.path.join(directory, filename) 
        allFiles.append(file_path)
    result = tests_problem_concurrent(allFiles, prompts, maxTokens=2000, sheetName = 'Sheet1', max_workers=10)
