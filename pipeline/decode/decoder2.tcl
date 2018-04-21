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
    opcode_length_decoder.v \
    ucontrol_store.v \
    sib_disp_detector.v \
    immediate_detector.v \
    modrm_detector.v \
    offset_detector.v \
    modrm_pointer.v \
    offset_selector.v \
    disp_selector.v \
    imm_selector.v \
    prefix_decoder.v \
    prefix_checker.v \
    modrm_selector.v \
    sib_selector.v \
    instruction_length_decoder.v \
    decode_stage1.v \
    decode_stage2.v \
};

analyze -sv {decoder2_test.sv};

#Elaborating the design
elaborate -top {decode_stage2};

#You will need to add commands below

#Set the clock
clock -clear; clock clk

#Set Reset
reset -expression {reset};

#Prove all
prove -bg -all

