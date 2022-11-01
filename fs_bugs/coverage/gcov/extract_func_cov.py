import glob
import csv
# apt-get install python3-bs4
# OR pip3 install beautifulsoup4
from bs4 import BeautifulSoup

xfstests_mcfs_res = []
test_names = ['xfstests', 'MCFS (more ops 1 hour)']

# Folder that contains all the gcov/lcov html files
html_folders = ['/Users/yifeiliu/Downloads/MCFS-cov-comparison-1029/sgdp05_xfstests_cov_out/fs/ext4',
                '/Users/yifeiliu/Downloads/MCFS-cov-comparison-1029/moreops_cov_out_1hour/fs/ext4']

# Get all *.func.html
for i in range(len(html_folders)):
    folder = html_folders[i]
    results = {}
    for fname in glob.glob(folder + '/*.func.html'):
        with open(fname) as fp:
            fname_key = fname.split('/')[-1].rsplit('.', 2)[0]
            func_val = {}
            soup = BeautifulSoup(fp, 'html.parser')
            cover_func_rows = soup.find_all("td", class_= "coverFn")

            for func_row in cover_func_rows:
                # Key: function name, Value: number of invocations
                # Note that the function invocation number could be 0
                func_val[str(func_row.text)] = int(func_row.find_next('td').text)

        results[fname_key] = func_val
    xfstests_mcfs_res.append(results)

# Write to two csv files
# xfstests_invoke_func.csv: functions that invoked in xfstests but not MCFS
# mcfs_invoke_func.csv: functions that invoked in MCFS but not xfstests

header = ['function_name', 'file_name', 'xfstests_invocations_count', 'mcfs_invocations_count']

xfst_invoke_f = open('xfstests_invoke_func.csv', 'w')
mcfs_invoke_f = open('mcfs_invoke_func.csv', 'w')
xfst_omit_f = open('xfstests_omit_func.csv', 'w')

xfst_csvwriter = csv.writer(xfst_invoke_f) 
mcfs_csvwriter = csv.writer(mcfs_invoke_f) 
xfst_omit_csvwriter = csv.writer(xfst_omit_f) 

xfst_csvwriter.writerow(header)
mcfs_csvwriter.writerow(header)
xfst_omit_csvwriter.writerow(header)

for file_name in xfstests_mcfs_res[0]:
    xfstests_kv = xfstests_mcfs_res[0][file_name]
    mcfs_kv = xfstests_mcfs_res[1][file_name]
    for func_name in xfstests_kv:
        row = [func_name, file_name, xfstests_kv[func_name], mcfs_kv[func_name]]
        if xfstests_kv[func_name] == 0:
            xfst_omit_csvwriter.writerow(row)
        if xfstests_kv[func_name] > 0 and mcfs_kv[func_name] == 0:
            xfst_csvwriter.writerow(row)
        elif xfstests_kv[func_name] == 0 and mcfs_kv[func_name] > 0:
            mcfs_csvwriter.writerow(row)

xfst_omit_f.close()
mcfs_invoke_f.close()
xfst_invoke_f.close()

"""
for i in range(len(xfstests_mcfs_res)):
    res = xfstests_mcfs_res[i]
    print(test_names[i])
    for res_key, res_value in res.items():
        print('Filename : ', res_key)
        for func_key, func_value in res_value.items():
            print('Function name: ', func_key, '---', 'Invocation times: ', func_value)
    print('********************')
"""

"""
if (len(xfstests_mcfs_res[0].keys()) != len(xfstests_mcfs_res[1].keys())):
    print('ERROR: file count is not equal')

for file_name in xfstests_mcfs_res[0]:
    if (len(xfstests_mcfs_res[0][file_name].keys()) != len(xfstests_mcfs_res[1][file_name].keys())):
        print('ERROR: function count is not equal for file ', file_name)
"""
