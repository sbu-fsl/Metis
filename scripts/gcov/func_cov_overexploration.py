import glob
import csv
# apt-get install python3-bs4
# OR pip3 install beautifulsoup4
from bs4 import BeautifulSoup

# Goals: 
# 1. find out over-explored functions (with the corresponding files)
# 2. find out the files whose percentage and lines are under-covered

# EDIT this folder, which contains all the *.func.html
folder = '/Users/yifeiliu/Downloads/MCFS-cov-comparison-1029/sgdp05_mcfs_cov_out_journal60mins/fs/ext4'

# Key: file name; Value: sub-dict with file name as key, function:hitcount as value
results = {}

# Dict where Key: function name; value: hit count
all_funcs = {}

# Dict where Key: file name; value: list ['lines_hit', 'lines_miss', 'lines_total', 'line_hit_percentage']
files_line = {}

for fname in glob.glob(folder + '/*.func.html'):
    with open(fname) as fp:
        fname_key = fname.split('/')[-1].rsplit('.', 2)[0]
        func_val = {}
        # For functions
        soup = BeautifulSoup(fp, 'html.parser')
        cover_func_rows = soup.find_all("td", class_= "coverFn")
        # For files
        file_meta_rows = soup.find_all("td", class_= "headerItem")
        lines_hit_total = file_meta_rows[1].find_next_siblings('td', 'headerCovTableEntry')
        hit_cnt = int(lines_hit_total[0].text)
        total_cnt = int(lines_hit_total[1].text)
        files_line[fname_key] = [hit_cnt, total_cnt - hit_cnt, total_cnt, round(hit_cnt / total_cnt * 100, 1)]

        for func_row in cover_func_rows:
            # Key: function name, Value: number of invocations
            # Note that the function invocation number could be 0
            func_val[str(func_row.text)] = int(func_row.find_next('td').text)
            all_funcs[str(func_row.text)] = [int(func_row.find_next('td').text), fname_key]
    results[fname_key] = func_val

# all_funcs = {k: v for k, v in sorted(all_funcs.items(), key=lambda item: item[1])}
# print('all_funcs: ', all_funcs)
# print('results: ', results)

func_header = ['function_name', 'file_name', 'hit_count']
file_header = ['file_name', 'lines_hit', 'lines_miss', 'lines_total', 'percentage_hit']

func_hit_f = open('all_funcs_mcfs_ext4.csv', 'w')
file_hit_f = open('file_mcfs_ext4.csv', 'w')

func_writer = csv.writer(func_hit_f)
file_writer = csv.writer(file_hit_f)

func_writer.writerow(func_header)
file_writer.writerow(file_header)

func_rows = []
for name, vlist in all_funcs.items():
    row = [name, vlist[1], vlist[0]]
    func_rows.append(row)

func_writer.writerows(func_rows)

file_rows = []
for name, vlist in files_line.items():
    row = [name, vlist[0], vlist[1], vlist[2], vlist[3]]
    file_rows.append(row)

file_writer.writerows(file_rows)

file_hit_f.close()
func_hit_f.close()
