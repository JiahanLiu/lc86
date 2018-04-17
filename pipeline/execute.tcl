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
    ./common/basic_components/muxes.v \
    ./common/basic_components/logic_gates.v \
    ./common/flags/eflags.v \
    ./common/functional_units/adder.v \
    ./common/functional_units/shift_components.v \
    ./execute_components/alu.v \
    ./execute_components/execute_components.v \
    ./execute_components/mm_alu.v \
    ./execute_components/shifter.v \
    ./common/functional_units/subtract.v \
    ./execute.v \
};

analyze -sv {execute_test.sv};

#Elaborating the design
elaborate -top {execute};

#You will need to add commands below

#Set the clock
clock -clear; clock CLK

#Set Reset
reset -expression {RST};

#Prove all
prove -bg -all

