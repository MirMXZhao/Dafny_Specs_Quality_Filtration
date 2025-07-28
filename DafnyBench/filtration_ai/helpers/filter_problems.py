import os 
import pandas as pd
from formatted_prompts import prompts
import anthropic


ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
client = anthropic.Anthropic(api_key = ANTHROPIC_API_KEY)

def filter_problem(fileid, maxTokens = 100):     
    response = client.beta.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=maxTokens,
        system= [
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
    return response 

if __name__ == "__main__":
    df = pd.read_excel("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration_ai/fileids.xlsx")
    data = df.to_dict(orient="list")

    result =  {
        "filename": [],
        "fileid": [],
        "keepTrash": [],
        "violated": [],
        "reasoning": []
    }

    for i in range(1): # len(data["filename"])
        filename = data["filename"][i]
        fileid = data["id"][i]
        result["filename"].append(filename)
        result["fileid"].append(fileid)
        output = filter_problem(fileid)
        text = output.content[0].text
        lines = text.splitlines()
        result["keepTrash"].append(lines[0])
        result["violated"].append(lines[1])
        result["reasoning"].append(lines[2])
        if i%50 == 0:
            print("On the "+ str(i) + "th batch!")

        if i < 10:
            print("On the "+ str(i) + "th batch!")
            print("filename: " + filename)
            print(output)
    
    print(result)
    df = pd.DataFrame(data)
    df.to_excel('filterProblems.xlsx', sheet_name='Sheet1', index=False)


    
    