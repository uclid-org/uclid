# import required module
import enum
import os
from pathlib import Path
from random import seed
from random import random

# assign directory
src_directory = 'test'
dst_directory = 'parser_test/'

# global setting
src_file_num = 100
max_error = 3
max_error_type = 2
error_type = 2
error_number = 0
seed(os.times())

#this is the error more

def randomword(src_content):
    max_line = len(src_content)
    random_line = int(random()*max_line)
    count = 0 
    for line in  src_content:
        wordlist = list(line.split())
        if(count==random_line):
            random_column = int(random()*len(wordlist))
            if(len(wordlist)!=0):
                return " "+wordlist[random_column]+" "
            else :
                return " "
        count = count + 1
    
#have appendex error on one line
def error_0(srcfile,dstfile):
    global error_number
    src_content = srcfile.readlines()
    max_line = len(src_content)

    error_lines=[]

    #gather error line 
    for i in range(0,error_number+1):
        error_line = int(random()*max_line)
        error_lines.append(error_line)
    
    for error_line in error_lines:
        dstfile.write("//We have error on line "+str(error_line)+"\n")

    for count, line in enumerate(src_content):
        if(count in error_lines):
            #gather error element
            wordlist = list(line.split())
            max_column = len(wordlist)
            error_column = int(random()*max_column)
            this_line = "\t"
            cnt = 0
            for word in wordlist:
                if(cnt==error_column):
                    word = word + randomword(src_content)
                cnt = cnt + 1
                this_line = this_line + word
            this_line = this_line + "\n"
            dstfile.write(this_line)
        else :
            dstfile.write(line)
        
def error_1(srcfile,dstfile):
    global error_number
    src_content = srcfile.readlines()
    max_line = len(src_content)

    error_lines=[]

    #gather error line 
    for i in range(0,error_number+1):
        error_line = int(random()*max_line)
        error_lines.append(error_line)

    for error_line in error_lines:
        dstfile.write("//We have error on line "+str(error_line)+"\n")

    for count, line in enumerate(src_content):
        if(count in error_lines):
            #gather error element
            wordlist = list(line.split())
            max_column = len(wordlist)
            error_column = int(random()*max_column)
            this_line = "\t"
            cnt = 0
            for word in wordlist:
                if(cnt==error_column):
                    word = word + randomword(src_content)
                cnt = cnt + 1
            this_line = this_line + "\n"
            dstfile.write(this_line)
        else :
            dstfile.write(line)

def modify_file(srcfile,dstfile):
    global error_type
    global error_number
    if(error_type==0):
        #print("we should change to error_0")
        error_0(srcfile,dstfile)
        return
    if(error_type==1):
        #print("we should change to error_1")
        error_1(srcfile,dstfile)
        return
    for line in srcfile:
        dstfile.write(line)

def main():
    global error_type
    global error_number
    i = 0
    files = Path(src_directory).glob('*.ucl')
    for srcfilename in files:
        #use this part to loop over all the src file
        i = i + 1
        if(i>src_file_num):
            break

        #gather error types and number
        error_number = int(random()*max_error)+1
        error_type = int(random()*max_error_type)

        
        srcfile = open(srcfilename, "r")
        dstfilename = dst_directory + str(i)+".ucl"
        dstfile = open(dstfilename, "w")

        dstfile.write("//we gather "+str(error_number)+" Syntax Error\n")
        if(error_type==0):
            dstfile.write("//Error Type is More words\n")
        if(error_type==1):
            dstfile.write("//Error_Type is less words\n")
        dstfile.write("//src file is "+str(srcfile)+"\n")

        #modify the dstfile
        modify_file(srcfile,dstfile)

main()