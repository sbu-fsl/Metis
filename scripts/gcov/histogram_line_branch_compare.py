import os
import itertools
import re
import numpy as np
import csv

# assign directory
test_directory = '/newdisk/MCFS_Exp'
fs_directory1 = '/newdisk/MCFS_Exp/ext4'
fs_directory2 = '/newdisk/MCFS_Exp/xfstests/ext4'
op_dir = os.path.join(test_directory, 'histogram_op')
os.mkdir(op_dir, 0o777)
os.chdir(op_dir)
# iterate over files in
# that directory
HTMLFile1 = ''
HTMLFile2 = ''
filename1 = ''
filename2 = ''
fileexclusionlist = ['func', 'sort', 'index'] #Need to come up with logic for functional and dir link files
#for filename1, filename2 in itertools.zip_longest(sort_nicely(os.listdir(fs_directory1)), sort_nicely(os.listdir(fs_directory2))):
filenames1 = sorted( filter( lambda x: os.path.isfile(os.path.join(fs_directory1, x)), os.listdir(fs_directory1) ) )
filenames2 = sorted( filter( lambda x: os.path.isfile(os.path.join(fs_directory2, x)), os.listdir(fs_directory2) ) )

count = 0

for filename1, filename2 in itertools.zip_longest(filenames1, filenames2):
    f1 = os.path.join(fs_directory1, filename1)
    f2 = os.path.join(fs_directory2, filename2)
    if(filename1 == filename2):
        count += 1
    #checking if it is a file
    excluded1 = [ele for ele in fileexclusionlist if(ele in f1)]
    excluded2 = [ele for ele in fileexclusionlist if(ele in f2)]
    if (os.path.isfile(f1) and not excluded1) and (os.path.isfile(f2) and not excluded2):

        HTMLFile1 = f1
        HTMLFile2 = f2
        filename1 = os.path.basename(f1)
        filename2 = os.path.basename(f2)

        # Reading the file1
        htmldata1 = ''
        with open(HTMLFile1, 'r') as fp:
            for line in fp:
                    if "lineNum" in line and "Cov" in line:
                        htmldata1 += line

        # Reading the file2
        htmldata2 = ''
        with open(HTMLFile2, 'r') as fp:
            for line in fp:
                    if "lineNum" in line and "Cov" in line:
                        htmldata2 += line

        branches1 = re.findall(r'title=\"(.+?)\">', htmldata1)
        branches2 = re.findall(r'title=\"(.+?)\">', htmldata2)
        branch_exec1 = []
        branch_exec2 = []
        branch_counter = 1
        for b1 in branches1:
            b = re.findall(r'\d+', b1)
            if(len(b) == 1):
                #Not Executed branch
                branch = [branch_counter,0]
                branch_exec1.append(branch)
            else:
                branch_exec1.append([branch_counter, int(b[1])])
            
            branch_counter += 1
        
        branch_counter = 1
        for b2 in branches2:
            b = re.findall(r'\d+', b2)
            if(len(b) == 1):
                #Not Executed branch
                branch = [branch_counter,0]
                branch_exec2.append(branch)
            else:
                branch_exec2.append([branch_counter, int(b[1])])
            
            branch_counter += 1
        
        with open(filename1 + '_branch_compare.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL) 

            w.writerow(['Branch Number', 'Execution Count'])

            for branch in branch_exec1:
                w.writerow([branch[0], branch[1]])
        
        with open(filename2 + '_xfstests_branch_compare.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL) 

            w.writerow(['Branch Number', 'Execution Count'])

            for branch in branch_exec2:
                w.writerow([branch[0], branch[1]])

        htmldata1 = re.sub('<[^>]+>', '', htmldata1)
        htmldata2 = re.sub('<[^>]+>', '', htmldata2)

        html_split_colon1 = [[y for y in x.split(':')] for x in htmldata1.split('\n')]
        html_split_colon2 = [[y for y in x.split(':')] for x in htmldata2.split('\n')]

        covered_lines1 = []
        covered_branches1 = []

        for colon in html_split_colon1[:-1]:
            br_cov = 0
            br_not_cov = 0
            br_not_exc = 0

            for br in colon[0].split()[1:]:
                if '+' in br:
                    br_cov += 1
                elif '-' in br:
                    br_not_cov += 1
                elif '#' in br:
                    br_not_exc += 1
            if(br_cov != 0 or br_not_cov != 0 or br_not_exc != 0):
                branch_cov = []
                branch_cov.append(br_cov)
                branch_cov.append(br_not_cov)
                branch_cov.append(br_not_exc)
                covered_branches1.append(branch_cov)

            if len(colon) > 1:
                cmdinfo = []   
                cmdinfo.append(colon[0].split()[0])
                for item in colon[1:]:
                    cmdinfo.append(item)

                covered_lines1.append(cmdinfo)

        with open(filename1 + '.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL) 

            w.writerow(['LineNum','RunCount','Cmd'])

            for line in covered_lines1:
                w.writerow([int(line[0]), int(line[1]), line[2]])
        
        with open(filename1 + '_branch.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL)

            w.writerow(['BranchCovered','BranchNotCovered', 'BranchNotExecuted']) 

            for br in covered_branches1:
                w.writerow([br[0], br[1], br[2]])

        covered_lines2 = []
        covered_branches2 = []

        for colon in html_split_colon2[:-1]:
            br_cov = 0
            br_not_cov = 0
            br_not_exc = 0

            for br in colon[0].split()[1:]:
                if '+' in br:
                    br_cov += 1
                elif '-' in br:
                    br_not_cov += 1
                elif '#' in br:
                    br_not_exc += 1

            if(br_cov != 0 or br_not_cov != 0 or br_not_exc != 0):
                branch_cov = []
                branch_cov.append(br_cov)
                branch_cov.append(br_not_cov)
                branch_cov.append(br_not_exc)
                covered_branches2.append(branch_cov)

            if len(colon) > 1:
                cmdinfo = []   
                cmdinfo.append(colon[0].split()[0])
                for item in colon[1:]:
                    cmdinfo.append(item)

                covered_lines2.append(cmdinfo)

        with open(filename2 + '_xfstests.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL)

            w.writerow(['LineNum','RunCount','Cmd']) 

            for line in covered_lines2:
                w.writerow([int(line[0]), int(line[1]), line[2]])
        
        with open(filename2 + '_xfstests_branch.csv', 'w') as f:
            w = csv.writer(f, quoting=csv.QUOTE_ALL)

            w.writerow(['BranchCovered','BranchNotCovered', 'BranchNotExecuted']) 

            for br in covered_branches2:
                w.writerow([br[0], br[1], br[2]])

        try:
            import matplotlib.pyplot as plt
            import pandas as pd
        except ImportError:
            import pip
            pip.main(['install', '--user', 'matplotlib'])
            import matplotlib.pyplot as plt
            pip.main(['install', '--user', 'pandas'])
            import pandas as pd

        data1 = pd.read_csv(filename1 + '.csv', sep=',', usecols=['LineNum', 'RunCount'])
        data2 = pd.read_csv(filename2 + '_xfstests' + '.csv', sep=',', usecols=['LineNum', 'RunCount'])

        plt.rcParams["figure.figsize"] = (18, 12)

        plt.bar(data1['LineNum'], data1['RunCount'], alpha=0.5, label='MCFS', color ='green', align="center", log=True)
        plt.bar(data2['LineNum'], data2['RunCount'], alpha=0.5, label='XFS', color = 'maroon', align="center", log=True)

        
        plt.legend(loc = 'best')

        plt.ylabel('Execution Count (Log Scale)')
        plt.yscale('symlog')
        # #plt.xscale('symlog')
        plt.xlabel('Line Number')
        plt.title('Execution Count Vs Line Number')
        plt.savefig(filename1 + '.png')
        plt.close()

        branches_test1 = pd.read_csv(filename1 + '_branch_compare.csv', sep=',')
        branches_test2 = pd.read_csv(filename2 + '_xfstests_branch_compare.csv', sep=',')
        plt.rcParams["figure.figsize"] = (18, 12)

        if(not(branches_test1.empty or branches_test2.empty)):
            plt.ylim(bottom = 0, top = 1.5 * max(branches_test1['Execution Count'].max(), branches_test2['Execution Count'].max()))

        plt.bar(branches_test1['Branch Number'], branches_test1['Execution Count'], alpha=0.5, label='MCFS', color ='green', align="center", log=True)
        plt.bar(branches_test2['Branch Number'], branches_test2['Execution Count'], alpha=0.5, label='XFS', color = 'maroon', align="center", log=True)
        plt.legend(loc = 'best')
        plt.yscale('symlog')
        plt.title('Execution Count Vs Branch Number')
        plt.ylabel('Execution Count (Log Scale)')
        plt.xlabel('Branch Number')

        plt.savefig(filename1 + 'branch_compare.png')
        plt.close()



        branch_data1 = pd.read_csv(filename1 + '_branch.csv', sep=',')
        branch_data2 = pd.read_csv(filename2 + '_xfstests_branch.csv', sep=',')

        plt.ylim(bottom = 0, top = max(branch_data1['BranchCovered'].sum() + branch_data1['BranchNotCovered'].sum() + branch_data1['BranchNotExecuted'].sum(),
        branch_data2['BranchCovered'].sum() + branch_data2['BranchNotCovered'].sum() + branch_data2['BranchNotExecuted'].sum()))

        plt.bar('MCFS' , branch_data1['BranchCovered'].sum(), alpha=0.5, label='MCFS', color='blue')
        plt.bar('XFS', branch_data2['BranchCovered'].sum(), alpha=0.5, label='XFS', color='red')
        plt.legend(loc = 'best')
        plt.ylabel('Branches')

        plt.savefig(filename1 + 'branch.png')
        plt.close()

        with open(filename1 + '.txt', 'w') as fp:
            fp.write(htmldata1)
        
        with open('xfstests_' + filename2 + '.txt', 'w') as fp:
            fp.write(htmldata2)

        try:
            import html_to_json
        except ImportError:
            import pip
            pip.main(['install', '--user', 'html_to_json'])
            import html_to_json
        output_json1 = html_to_json.convert(htmldata1)
        output_json2 = html_to_json.convert(htmldata2)

        import json

        with open(filename1 + 'result.json', 'w') as fp:
            json.dump(output_json1, fp, indent = 1)
        
        with open('xfstests_' + filename2 + 'result.json', 'w') as fp:
            json.dump(output_json2, fp, indent = 1)
    
    # if(count == 12):
    #     break

print(count)
