#
# Copyright (c) 2020-2024 Yifei Liu
# Copyright (c) 2020-2024 Ajay Hegde
# Copyright (c) 2020-2024 Wei Su
# Copyright (c) 2020-2024 Erez Zadok
# Copyright (c) 2020-2024 Stony Brook University
# Copyright (c) 2020-2024 The Research Foundation of SUNY
#
# You can redistribute it and/or modify it under the terms of the Apache License, 
# Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
#

import os
# assign directory
test_directory = '/newdisk/MCFS_Exp'
fs_directory = '/newdisk/MCFS_Exp/ext4'
op_dir = os.path.join(test_directory, 'histogram_op')
os.mkdir(op_dir, 0o777)
os.chdir(op_dir)
# iterate over files in
# that directory
HTMLFile = ''
filename = ''
fileexclusionlist = ['func', 'sort', 'index'] #Need to come up with logic for functional and dir link files
for filename in os.listdir(fs_directory):
    f = os.path.join(fs_directory, filename)
    # checking if it is a file
    #print(f)
    excluded = [ele for ele in fileexclusionlist if(ele in f)]
    if os.path.isfile(f) and not excluded:
        #print(f)
        HTMLFile = f
        filename = os.path.basename(f)  

        # Reading the file
        htmldata = ''
        with open(HTMLFile, 'r') as fp:
            for line in fp:
                    if "lineNum" in line and "Cov" in line:
                        htmldata += line
                        #print(line) # The newline is included in line
        #htmldata = HTMLFile.read()
        import re
        htmldata = re.sub('<[^>]+>', '', htmldata)

        #data1 = re.split(' :', htmldata)
        #data0 = [x.split('" ",:," "') for x in data2.split('\n')]
        html_split_colon = [[y for y in x.split(':')] for x in htmldata.split('\n')]

        covered_lines = []
        max_y = 0
        max_x = 0

        for colon in html_split_colon[:-1]:
            lineinfo = colon[0]
            linecmd = colon[1]
            temp = lineinfo.split()
            temp = ([int(y) for y in temp])
            linenum = temp[0]
            runcount = temp[1]
            # print(linenum)
            # print(runcount)
            # print(linecmd)
            cmdinfo = []
            cmdinfo.append(linenum)
            cmdinfo.append(runcount)
            cmdinfo.append(linecmd)
            covered_lines.append(cmdinfo)
            if linenum > max_x:
                max_x = linenum
            if runcount > max_y:
                max_y = runcount


        import csv
        with open(filename + '.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL) 

            for line in covered_lines:
                w.writerow([line[0], line[1], line[2]])

        try:
            import matplotlib.pyplot as plt
            import pandas as pd
        except ImportError:
            import pip
            pip.main(['install', '--user', 'matplotlib'])
            import matplotlib.pyplot as plt
            pip.main(['install', '--user', 'pandas'])
            import pandas as pd


        data = pd.read_csv(filename + '.csv', sep=',',header=None, index_col =0)

        data.plot(kind='bar')
        # To specify the number of ticks on both or any single axes
        plt.locator_params(axis='y', nbins=10)
        plt.locator_params(axis='x', nbins=10)

        plt.ylabel('Execution Count')
        plt.yscale('symlog')
        #plt.xscale('symlog')
        plt.xlabel('Line Number')
        plt.title('Execution Count Vs Line Number')
        plt.savefig(filename + '.png')
        plt.close()
        #plt.show()

        # print(data0[1][0])
        # print(data3[0])

        with open(filename + '.txt', 'w') as fp:
            fp.write(htmldata)

        try:
            import html_to_json
        except ImportError:
            import pip
            pip.main(['install', '--user', 'html_to_json'])
            import html_to_json
        output_json = html_to_json.convert(htmldata)

        #for i in output_json['html'][0]['body'][0]['table'][1]['tr'][1]['td'][0]['pre']:
        # for i in output_json['a']:
        #     for j in i['span'][1]['_value']:
        #         print(j)

        import json

        with open(filename + 'result.json', 'w') as fp:
            json.dump(output_json, fp, indent = 1)

