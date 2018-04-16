#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

#Reading the files 
analyze -v2k {
    /home/projects/courses/spring_16/ee382n-16785/lib/time \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib1 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib2 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib3 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib4 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib5 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib6 \
    ./common/cache_and_registers/register_file_decoder.v \
    ./common/cache_and_registers/registers.v \
};

analyze -sv {registers_test.sv};

#Elaborating the design
elaborate -top {register_file};

#You will need to add commands below

#Set the clock
clock -clear; clock CLK -both_edges

#Set Reset
reset -expression {RST};

#Prove all
prove -bg -all

