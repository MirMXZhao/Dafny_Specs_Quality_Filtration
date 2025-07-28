import json
import os 

# Load from file
with open('/Users/cinnabon/Documents/MIT/UROP_2025/DafnyComp/dafnycomp_300.json', 'r') as f:
    data = json.load(f)

# data is now a list of dictionaries
print(f"Number of entries: {len(data)}")
output_dir = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyComp/dafnyCompFiles"
for i in range(len(data)):
    if i%30 == 0: 
        entry = data[i]
        org_id = entry.get("org_input_id", "unknown_id")

        # Clean filename just in case
        filename = f"{org_id}.dfy"
        filepath = os.path.join(output_dir, filename)

        with open(filepath, 'w') as out_file:
            out_file.write("Original Input:\n")
            out_file.write(entry.get("org_input", "") + "\n\n")
            out_file.write("Ground Truth Output:\n")
            out_file.write(entry.get("gt_output", ""))