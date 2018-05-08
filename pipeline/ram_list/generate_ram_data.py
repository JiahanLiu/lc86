#!/usr/bin/python
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4

import getopt, sys

def generate_memory(filename):
    tagfilelist = []
    ramfilelist = []
    for i in xrange(0, 4):
        taglist = open("tag_ram%d.list" % i, 'w')
        tagfilelist.append(taglist)

        ramfilelist0 = []
        for j in xrange(0, 16):
            ramfile = open('ram%d_%d.list' % (i, j), 'w')
            ramfilelist0.append(ramfile)
        ramfilelist.append(ramfilelist0)

    with open(filename, 'r') as lstfile:
        memory = []
        global_address = 0 
        first_addr_flag = 1
        for line in lstfile:
            row = line.split()
            # print row
            for entry in row:
                # print entry
                if entry.startswith('//'):
                    break
                elif entry.endswith(':'):
                    address = entry.replace(':', '')
                    address = int(address, 16)
                    if first_addr_flag:
                        global_address = address
                        first_addr_flag = 0
                else:
                    memory.append((global_address, entry))
                    global_address += 1
        
        print memory
        ramsetnumlist = []
        cachesetnumlist = []
        cachesetnumlist1 = []
        cachesetnumlist2 = []
        for (address, data) in sorted(memory, key=lambda x:x[0]):
            ram_set_num = address / 128
            if ram_set_num not in ramsetnumlist:
                ramsetnumlist.append(ram_set_num)

            # print ram_set_num
            if address < 0x2000:
                cache_set_num = address >> 9
                if cache_set_num not in cachesetnumlist:
                    cachesetnumlist.append(cache_set_num)

                ram_num = address % 16
                # print ram_num
                ramfilelist[ram_set_num][ram_num].write(data)
                ramfilelist[ram_set_num][ram_num].write('\n')
            elif address < 0x4000:
                cache_set_num = address > 9
                if cache_set_num not in cachesetnumlist1:
                    cachesetnumlist1.append(cache_set_num)

                ram_num = address % 16
                ramfilelist[1][ram_num].write(data)
                ramfilelist[1][ram_num].write('\n')
            else:
                cache_set_num = address >> 9
                if cache_set_num not in cachesetnumlist2:
                    cachesetnumlist2.append(cache_set_num)

                ram_num = address % 16
                ramfilelist[2][ram_num].write(data)
                ramfilelist[2][ram_num].write('\n')   

#        for num in ramsetnumlist:
#            print "%x" % num,
#        print '\n'
        
#        for num in cachesetnumlist:
#            print "%02x" % num
        for tag in cachesetnumlist:
            for i in xrange(0, 8):
                tagfilelist[0].write("%02x\n" % tag)

        for tag in cachesetnumlist1:
            for i in xrange(0, 8):
                tagfilelist[1].write("%02x\n" % tag)

        for tag in cachesetnumlist2:
            for i in xrange(0, 8):
                tagfilelist[2].write("%02x\n" % tag)
            
    for i in xrange(0, 4):
        tagfilelist[i].close()
        for j in xrange(0,16):
            ramfilelist[i][j].close()

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
