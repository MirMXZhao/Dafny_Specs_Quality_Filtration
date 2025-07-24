import pandas as pd

df = pd.read_excel("output.xlsx")
data = df.to_dict(orient="list")


def invalidity(idx):
    complexity = 10
    total = data["num_methods"][idx] + data["num_lemmas"][idx] + data["num_functions"][idx] + data["num_classes"][idx] + data["num_predicates"][idx] 
    if total >= complexity or data["num_none_either"][idx] >= 3 or total == 0:
        # print(data["file_label"][idx])
        return True
        
    return False 

if __name__ == "__main__":
    count = 0
    for i in range(len(data["file_label"])):
        if invalidity(i):
            count += 1 
    print(count)
