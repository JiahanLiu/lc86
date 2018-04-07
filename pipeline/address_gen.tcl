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
    ../execution_core/basic_components/muxes.v \
    ../execution_core/basic_components/logic_gates.v \
    ../execution_core/basic_components/eflags.v \
    ../execution_core/functional_units/adder.v \
    ../execution_core/functional_units/alu.v \
    ./segment_limit_check.v \
    ./reg_dependency_check.v \
    common.v \
    address_generation.v \
};

analyze -sv {address_gen_test.sv};

#Elaborating the design
elaborate -top {address_generation};

#You will need to add commands below

#Set the clock
clock -clear; clock CLK

#Set Reset
reset -expression {RST};

#Prove all
prove -bg -all

