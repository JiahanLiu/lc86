#!/usr/bin/python
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4

import getopt, sys, csv

wire1_str = "wire %s;\n"
wiren_str = "wire [%d:0] %s;\n"
assign_str = "assign %s = CONTROL_STORE[%d:%d];\n"

def generate_signals(filename):
    wirefile = open('control_store_wires.v', 'w')
    assignfile = open('control_store_signals.v', 'w')

    romfilelist = []
    for i in xrange(0, 9):
        romfilelist0 = []
        for j in xrange(0, 2):
            romfile = open('rom%d_%d.list' % (i, j), 'w')
            romfilelist0.append(romfile)
        romfilelist.append(romfilelist0)

    num_signals = 128

    desccol = 1
    opcodecol = desccol + 1
    addrcol = opcodecol + 1
    signalcol = addrcol + 1
    maxcol = signalcol + num_signals
    cs_sr1_d2_pos = 15
    with open(filename, 'rb') as csvfile:
        csvreader = csv.reader(csvfile, delimiter=',', quotechar='"')
        row_num = 1
        for row in csvreader:
            if row_num == 1:
                col_num = 1
                pos = num_signals - 1
                signal_name = ""
                signal_pos = num_signals - 1
                for signal in row:
                    if col_num >= signalcol and col_num <= maxcol:
                        if signal == 'CS_SR1_D2':
                            cs_sr1_d2_pos = num_signals - pos - 1
                            # print cs_sr1_d2_pos
                        if signal or pos == -1:
                            if pos < (num_signals - 1):
                                assignfile.write(assign_str % (signal_name, signal_pos, pos+1))
                                if signal_pos == (pos+1):
                                    wirefile.write(wire1_str % signal_name)
                                else:
                                    wirefile.write(wiren_str % (signal_pos-(pos+1), signal_name))
                            signal_name = signal
                            signal_pos = pos
                        pos -= 1
                    col_num += 1

            else:
                col_num = 1
                rom_num = 0
                current_row = [[], []]
                entries = 1
                for signal in row:
                    if col_num == desccol:
                        desc = signal
                    if col_num == opcodecol:
                        opcode_full = signal
                        if "+r" in signal:
                            entries = 8
                            if "+r7" in signal:
                                entries = 7
                            # TODO: change +r to have different registers encoded
                    if col_num == addrcol:
                        opcode = int(signal, 16)
                        rom_addr = opcode & 0x1F
                        rom_num = (opcode >> 5) & 0xF
                        if rom_num > 8:
                            rom_num = 8
                        # print "%x %x %x" % (rom_addr, rom_num, opcode)
                        for j in xrange(0, 2):
                            romfilelist[rom_num][j].write("@%02x" % (rom_addr))
                            romfilelist[rom_num][j].write(" // %s (%s)\n" % (desc, opcode_full))
                    elif col_num >= signalcol and col_num <= maxcol:
                        if (signal == 'x'):
                            signal = '0'

                        if col_num < (signalcol + 64):
                            current_row[0].append(signal)
                        else:
                            current_row[1].append(signal)

                        if col_num < (signalcol + 64): # first set of roms 
                            romfilelist[rom_num][0].write(signal)
                        else:
                            romfilelist[rom_num][1].write(signal)
                    col_num += 1
                for j in xrange(0, 2):
                    if 'x' in current_row[j]:
                        romfilelist[rom_num][j].write("\n")
                    else:
                        romfilelist[rom_num][j].write("  // 0x%X\n" % int(''.join(current_row[j]), 2))

                reg_offset = 0
                if entries == 7:
                    reg_offset = 1
                for i in xrange(1, entries):
                    # cs_sr1_d2_pos = 15
                    if entries > 1:
                        bit2 = str(((i+reg_offset) >> 2) & 0x1)
                        bit1 = str(((i+reg_offset) >> 1) & 0x1)
                        bit0 = str(((i+reg_offset) >> 0) & 0x1)
                        current_row[0][cs_sr1_d2_pos] = bit2[0]
                        current_row[0][cs_sr1_d2_pos+1] = bit1[0]
                        current_row[0][cs_sr1_d2_pos+2] = bit0[0]
                    for j in xrange(0, 2):
                        romfilelist[rom_num][j].write(''.join(current_row[j]))
                        romfilelist[rom_num][j].write("\n")
            row_num += 1

    wirefile.close()
    assignfile.close()

    for i in xrange(0, 9):
        for j in xrange(0, 2):
            romfilelist[i][j].close()

def main():
    shortopts = "hf:v"
    longopts = ["help", "filename="]
    usage = "-h -f <csv file>"

    try:
        opts, args = getopt.getopt(sys.argv[1:], shortopts, longopts)
    except getopt.GetoptError as err:
        # print help information and exit:
        print str(err)  # will print something like "option -a not recognized"
        print usage
        sys.exit(2)

    filename = "control_store.csv"
    verbose = False

    for o, a in opts:
        if o == "-v":
            verbose = True
        elif o in ("-h", "--help"):
            print usage
            sys.exit()
        elif o in ("-f", "--filename"):
            filename = a
        else:
            assert False, "unhandled option"

    generate_signals(filename)

if __name__ == "__main__":
    main()
