#!/usr/bin/python
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4

import getopt, sys

file_str = 'blk_line%d_sram%d.list'

def generate_memory(filename):
    ramfilelist = []
    for i in xrange(0, 8):
        ramfilelist0 = []
        for j in xrange(0, 32):
            ramfile = open(file_str % (i, j), 'w')
            ramfilelist0.append(ramfile)
        ramfilelist.append(ramfilelist0)

    with open(filename, 'r') as lstfile:
        memory = []
        global_address = 0 
        for line in lstfile:
            row = line.split()
            # print row
            for entry in row:
                # print entry
                if entry.startswith('//') or not entry:
                    break
                elif entry.endswith(':'):
                    address = entry.replace(':', '')
                    address = int(address, 16)
                    # print "ADDRESS: %x" % address
                    if global_address != address:
                        global_address = address
                        # print "GLOBAL %x" % global_address
                else:
                    memory.append((global_address, entry))
                    global_address += 1
        
        # print memory
        for (address, data) in sorted(memory, key=lambda x:x[0]):
            blk_line = (address >> 12) & 0x7 # address[14:12]
            sram_num = address & 0x1F # address[4:0]
            row_num = (address >> 5) & 0x7F # address[11:5]

            # print "blk_line %d sram_num %d\n" % (blk_line, sram_num)
            ramfilelist[blk_line][sram_num].write("@%02x\n%s\n" % (row_num, data))
            #ramfilelist[blk_line][sram_num].write(data)
            #ramfilelist[blk_line][sram_num].write("\n")


    for i in xrange(0, 8):
        for j in xrange(0, 32):
            print '$readmemh("blk_line%d_sram%d.list", main_memory_u.blk_line%d.sram%d.mem)' % (i, j, i, j)

    for i in xrange(0, 8):
        for j in xrange(0, 32):
            ramfilelist[i][j].close()

def main():
    shortopts = "hf:v"
    longopts = ["help", "filename="]
    usage = "-h -f <lst file>"

    try:
        opts, args = getopt.getopt(sys.argv[1:], shortopts, longopts)
    except getopt.GetoptError as err:
        # print help information and exit:
        print str(err)  # will print something like "option -a not recognized"
        print usage
        sys.exit(2)

    filename = "exception_test.lst"
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

    generate_memory(filename)

if __name__ == "__main__":
    main()
