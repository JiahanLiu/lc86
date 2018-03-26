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
        romfile = open('rom%d.list' % i, 'w')
        romfilelist.append(romfile)

    desccol = 1
    opcodecol = desccol + 1
    addrcol = opcodecol + 1
    signalcol = addrcol + 1
    maxcol = 59
    with open(filename, 'rb') as csvfile:
        csvreader = csv.reader(csvfile, delimiter=',', quotechar='"')
        row_num = 1
        for row in csvreader:
            if row_num == 1:
                col_num = 1
                pos = 63
                signal_name = ""
                signal_pos = 63
                for signal in row:
                    if col_num >= signalcol and col_num <= maxcol:
                        if signal:
                            if pos < 63:
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
                current_row = []
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
                        romfilelist[rom_num].write("@%02x" % (rom_addr))
                        romfilelist[rom_num].write(" // %s (%s)\n" % (desc, opcode_full))
                    elif col_num >= signalcol and col_num <= maxcol:
                        if entries:
                            current_row.append(signal)
                        romfilelist[rom_num].write(signal)
                    col_num += 1
                romfilelist[rom_num].write("\n")

                for i in xrange(1, entries):
                    romfilelist[rom_num].write(''.join(current_row))
                    romfilelist[rom_num].write("\n")
            row_num += 1

    wirefile.close()
    assignfile.close()

    for i in xrange(0, 9):
        romfilelist[i].close()

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
