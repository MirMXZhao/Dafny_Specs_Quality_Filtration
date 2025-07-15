import os 
import pandas as pd
from formatted_prompts import prompts
import anthropic


ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
client = anthropic.Anthropic(api_key = ANTHROPIC_API_KEY)

# def test_file_upload():
#     response = client.beta.messages.create(
#         model="claude-sonnet-4-20250514",
#         max_tokens=500,
#         messages=[
#             {
#                 "role": "user",
#                 "content": [
#                     {
#                         "type": "text",
#                         "text": "output the first three lines of the following file"
#                     },
#                     {
#                         "type": "document",
#                         "source": {
#                             "type": "file",
#                             "file_id": "file_011CR9Rj1QMCbJaor3Nf5Ex1"
#                         }
#                     }
#                 ]
#             }
#         ],
#         betas=["files-api-2025-04-14"],
#     )
#     return response 

def check_body(filepath, maxTokens = 10):
    with open(filepath, 'r') as f: 
        content = f.read()
    print(content)
    response = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens= maxTokens,
        temperature=0.8,
        system= prompts["check_bodies"]["task"],
        messages=[
            {
                "role": "user",
                "content": [
                    { 
                        "type": "text",
                        "text": prompts["check_bodies"]["output_request"] + prompts["check_bodies"]["file"]
                    },
                    {
                        "source": {
                            "type": "file",
                            "file_id": "file_011CR9QMdxYxzenuEUZuU8Gu"
                        }
                    }
                ]
            }
        ]
    )
    return response 

if __name__ == "__main__":
    # testFilepath = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/test.dfy"
    # res = check_body(testFilepath)
    # print(res) 
    # print(res.content[0].text)
    df = pd.read_excel("fileids.xlsx")
    data = df.to_dict(orient="list")

    result =  {
        "filename": [],
        "output": []
    }

    for fileid in range(data):
        output = check_body(file)
        result["filename"].append(file)
        result["output"].append(output)

    
    

