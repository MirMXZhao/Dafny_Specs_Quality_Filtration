import anthropic 
import os 
import pandas as pd

ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
client = anthropic.Anthropic(api_key = ANTHROPIC_API_KEY)

def upload(directory, filename):
    filepath = os.path.join(directory, filename)
    result = client.beta.files.upload(
        file=(filename, 
            open(filepath, "rb"), 
            "text/plain"), 
    )
    return result

if __name__ == "__main__":
    # directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed"
    directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/filtered_and_tests"
    files = os.listdir(directory) 
    file_ids =  {
        "filename": [],
        "id": []
    }

    for file in files:
        output = upload(directory, file)
        file_ids["filename"].append(file)
        file_ids["id"].append(output.id)

    df = pd.DataFrame(file_ids)
    # To export to an Excel file
    df.to_excel('filteredFileids.xlsx', sheet_name='fileids', index=False)


