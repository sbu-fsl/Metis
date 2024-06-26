import csv
import datetime

def time_to_seconds(time_str):
    time_parts = list(map(int, time_str.split(':')))
    if len(time_parts) == 3:
        return time_parts[0] * 3600 + time_parts[1] * 60 + time_parts[2]
    elif len(time_parts) == 2:
        return time_parts[0] * 60 + time_parts[1]
    else:
        return time_parts[0]

input_csv = 'verifs2_pan_process_metrics.csv'  # Replace with your input CSV file name
output_csv = 'verifs2_pan_process_metrics_new.csv'  # Replace with your desired output CSV file name

# Read the input CSV file
with open(input_csv, 'r') as infile:
    reader = csv.DictReader(infile)
    rows = list(reader)

# Prepare the new header
new_header = [
    'pan_Elapsed Time (s)', 'pan_User Time (s)', 'pan_System Time (s)', 'pan_CPU Time (s)', 'pan_Memory Usage (bytes)', 'pan_Read Bytes', 'pan_Write Bytes',
    'verifs2_Elapsed Time (s)', 'verifs2_User Time (s)', 'verifs2_System Time (s)', 'verifs2_CPU Time (s)', 'verifs2_Memory Usage (bytes)', 'verifs2_Read Bytes', 'verifs2_Write Bytes'
]

# Prepare the data for the new CSV file
new_rows = []
for i in range(0, len(rows), 2):
    if rows[i]['Process'] == 'pan' and rows[i+1]['Process'] == 'verifs2':
        new_row = {
            'pan_Elapsed Time (s)': time_to_seconds(rows[i]['Elapsed Time (s)']),
            'pan_User Time (s)': rows[i]['User Time (s)'],
            'pan_System Time (s)': rows[i]['System Time (s)'],
            'pan_CPU Time (s)': rows[i]['CPU Time (s)'],
            'pan_Memory Usage (bytes)': rows[i]['Memory Usage (bytes)'],
            'pan_Read Bytes': rows[i]['Read Bytes'],
            'pan_Write Bytes': rows[i]['Write Bytes'],
            'verifs2_Elapsed Time (s)': time_to_seconds(rows[i+1]['Elapsed Time (s)']),
            'verifs2_User Time (s)': rows[i+1]['User Time (s)'],
            'verifs2_System Time (s)': rows[i+1]['System Time (s)'],
            'verifs2_CPU Time (s)': rows[i+1]['CPU Time (s)'],
            'verifs2_Memory Usage (bytes)': rows[i+1]['Memory Usage (bytes)'],
            'verifs2_Read Bytes': rows[i+1]['Read Bytes'],
            'verifs2_Write Bytes': rows[i+1]['Write Bytes']
        }
        new_rows.append(new_row)

# Write the transformed data to the output CSV file
with open(output_csv, 'w', newline='') as outfile:
    writer = csv.DictWriter(outfile, fieldnames=new_header)
    writer.writeheader()
    writer.writerows(new_rows)

print(f"Transformed CSV file written to {output_csv}")
