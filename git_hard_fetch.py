import os
import subprocess
from subprocess import PIPE, Popen


print("fetching")

#print(test_dirs)


shell_command = 'eval "$(ssh-agent -s)"'
P = subprocess.Popen(shell_command.split())
P.wait()
shell_command2 = 'ssh-add ../github'
P2 = subprocess.Popen(shell_command2.split())
P2.wait()
shell_command3 = 'git fetch --all'
P3 = subprocess.Popen(shell_command3.split())
P3.wait()
shell_command4 = 'git reset --hard origin/master'
P4 = subprocess.Popen(shell_command4.split())
P4.wait()