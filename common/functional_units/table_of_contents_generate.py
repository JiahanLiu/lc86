# Only Python 3 Compatible
input_file_name = input("Enter file name: ");

write_file_preparse = "table_of_contents_" + input_file_name;
write_file = "python_script_residues/" + write_file_preparse[:-1] + "txt";

comment_string = "// "

file_write = open(write_file, "w+");

print("", file=file_write);
print("//-------------------------------------------------------------------------------------", file=file_write);
print("// " + input_file_name, file=file_write);
print("// --------------------", file=file_write);
print("// EE382N, Spring 2018", file=file_write);
print("// Apurv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu", file=file_write);
print("//", file=file_write);

array_of_module_names = [];
array_of_functionalities = [];
with open(input_file_name, 'r') as file_read:
	for line_read in file_read:
		if(line_read[0:6] == "module"):
			index_of_end_name = line_read.index("(");
			module_name = line_read[7:index_of_end_name];
			array_of_module_names.append(module_name);
		if(line_read[0:17] == "// Functionality:"):
			function_line = line_read[18:];
			array_of_functionalities.append(function_line);

for i in range(0,len(array_of_module_names)):			
	print("// {:32s} - {:32s}".format(array_of_module_names[i], array_of_functionalities[i]).replace('\n',''), file=file_write);

print("//", file=file_write);
print("//-------------------------------------------------------------------------------------", file= file_write);

file_write.close();	
