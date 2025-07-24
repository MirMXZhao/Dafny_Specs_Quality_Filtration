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

# def check_body(fileid, maxTokens = 12):
#     response = client.beta.messages.create(
#         model= "claude-sonnet-4-20250514",
#         max_tokens= maxTokens,
#         temperature=0.8,
#         system= [
#             {
#                 "type": "text",
#                 "text": prompts["check_bodies"]["task"],
#                 "cache_control": {"type": "ephemeral"}
#             }
#         ],
#         messages=[
#             {
#                 "role": "user",
#                 "content": [
#                     { 
#                         "type": "text",
#                         "text": prompts["check_bodies"]["output_request"] + prompts["check_bodies"]["file"],
#                         "cache_control": {"type": "ephemeral"}
#                     },
#                     {
#                         "type": "document",
#                         "source": {
#                             "type": "file_id",
#                             "file_id": fileid
#                         }
#                     }
#                 ]
#             }
#         ]
#     )
#     return response 
def check_body(fileid, maxTokens = 12):     
    response = client.beta.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=maxTokens,
        system= [
            {
                "type": "text",
                "text": prompts["check_bodies"]["task"],
                "cache_control": {"type": "ephemeral"}
            }
        ],
        messages=[
            {
                "role": "user",
                "content": [
                    { 
                        "type": "text",
                        "text": prompts["check_bodies"]["output_request"] + prompts["check_bodies"]["file"],
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
    return response 

if __name__ == "__main__":
    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/fileids.xlsx")
    data = df.to_dict(orient="list")

    result =  {
        "filename": [],
        "fileid": [],
        "output": []
    }

    for i in range(5):
        filename = data["filename"][i]
        fileid = data["id"][i]
        result["filename"].append(filename)
        result["fileid"].append(fileid)
        output = check_body(fileid)
        trueFalse = output.content[0].text
        result["output"].append(trueFalse)
        if i%50 == 0:
            print("On the "+ str(i) + "th batch!")

        if i < 10:
            print("On the "+ str(i) + "th batch!")
            print("filename: " + filename)
            print(output)
    
    print(result)
    # df = pd.DataFrame(data)
    # df.to_excel('checkBodies.xlsx', sheet_name='Sheet1', index=False)


    
    

