import os
import subprocess
from subprocess import PIPE, Popen


print("running x86 single instruction tests")

test_dirs = next(os.walk('.'))[1]
#print(test_dirs)

with open('failed_tests', 'w+') as outfile:
	for dir_ in test_dirs:
		if(dir_ != 'DVEfiles'): 
			os.chdir(dir_)
			print("starting: " + dir_)
			shell_command = 'vcs -full64 -debug_all -f master +incdir+../../'
			P = subprocess.Popen(shell_command.split())
			P.wait()
			shell_command2 = './simv'
			P2 = subprocess.Popen(shell_command2.split(), stdout=subprocess.PIPE)
			P2.wait()
			for ln in P2.stdout:
				if('Error' == ln[0:5]):
					outfile.write(dir_ + '\n')
					outfile.write(ln);
					print(dir_ + '\n')
					print(ln)
		#outfile.write("Go Light it up");
		#test_dirs2 = next(os.walk('.'))[1]
		#print(test_dirs2)
		#subprocess.call(['./run_pipeline'])
		#subprocess.call(['./simv'])
		os.chdir('..')

