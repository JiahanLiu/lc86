analyze -v2k -v {
    /home/projects/courses/spring_16/ee382n-16785/lib/time \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib1 \
    ./lib2 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib3 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib4 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib5 \
    /home/projects/courses/spring_16/ee382n-16785/lib/lib6 \
}


analyze -v2k {
    ../common.v \
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
    decode_merge.v \
};

analyze -sv {decode_merge_test.sv};

#Elaborating the design
elaborate -top {PIPELINE};

#You will need to add commands below

#Set the clock
clock -clear; clock CLK

#Set Reset
reset -expression {RST};

#Prove all
prove -bg -all

