#!/usr/bin/env python

"""
lsba: List Source code by Address
"""

import sys
import getopt
import struct
import copy
import os


def usage():
    print "Usage: lsba [-e|--elf] elf_path [-l|--load] load_path"
    print "            [-a|-addr] 0xtarget_address"
    print "            [-h]"
    print ""
    print "       -e|--elf: specify full path of the ELF file"
    print "       -l|--load: specify full path of MAUI load"
    print "       -a|--addr: specify the target address"
    print "       -h: show this help"


def decode_uleb128(data, size):
    val = 0
    shift = 0
    len = 0
    for i in range(0, size):
        len += 1
        val |= (ord(data[i]) & 0x7f) << shift
        shift += 7
        if (ord(data[i]) & 0x80) == 0:
            break
    return (val, len)


def decode_leb128(data, size):
    val = 0
    shift = 0
    len = 0
    for i in range(0, size):
        len += 1
        val |= (ord(data[i]) & 0x7f) << shift
        shift += 7
        if (ord(data[i]) & 0x80) == 0:
            break
    if (shift < size) & ((ord(data[i]) & 0x40) != 0):
        val |= -(1 << shift)

    return (val, len)


def read_debug_line(data, size, target_addr, debug):
    # assume cannot-find by default
    result = [ "", "", "", -1 ]

    # initialize state machine
    sm = { "address" : 0, "file" : 1, "line" : 1, "column" : 0, "is_stmt" : 0, "basic_block" : "false", "end_sequence" : "false" }

    # define opcode
    DW_LNS_copy = 1
    DW_LNS_advance_pc = 2
    DW_LNS_advance_line = 3
    DW_LNS_set_file = 4
    DW_LNS_set_column = 5
    DW_LNS_negate_stmt = 6
    DW_LNS_set_basic_block = 7
    DW_LNS_const_add_pc = 8
    DW_LNS_fixed_advance_pc = 9
    DW_LNE_end_sequence = 1
    DW_LNE_set_address = 2
    DW_LNE_define_file = 3


    """
        execute the line number program
    """

    if debug == 1:
        print "execut the line number program"
        print ""

    indx = 0
    stmt_ptr = 0
    while 1:
        if debug == 1:
            print "indx =", indx, "size =", size
        if indx >= size:
            break;

        """
            read prologue
        """

        prologue = {}

        # read header
        temp = struct.unpack("<LHLBBBBB", data[indx: indx + 15])
        prologue["total_length"] = temp[0]
        prologue["version"] = temp[1]
        prologue["prologue_length"] = temp[2]
        prologue["minimum_instruction_length"] = temp[3]
        prologue["default_is_stms"] = temp[4]
        prologue["line_base"] = temp[5]
        prologue["line_range"] = temp[6]
        prologue["opcode_base"] = temp[7]
        stmt_ptr = indx + 4
        indx = indx + 15

        if debug == 1:
            print "prologue:"
            print "\n".join(["    %s = %d" % (s, d) for s, d in prologue.items()])

        # read starndard opcode lengths array
        std_opcode_len = []
        for i in range(0, prologue["opcode_base"] - 1):
            std_opcode_len.append(copy.copy(ord(data[indx])))
            indx = indx + 1
        prologue["standard_opcode_lengths"] = std_opcode_len

        if debug == 1:
            print "    standard_opcode_lengths =", prologue["standard_opcode_lengths"]

        # read include directories
        dir = []
        temp_dir = data[indx: i + prologue["total_length"]].split('\0')
        temp_len = 0
        for i in range(0, len(temp_dir)):
            dir.append(copy.copy(temp_dir[i]))
            if temp_dir[i] == '':
                temp_len += 1
                break
            else:
                temp_len += len(temp_dir[i]) + 1
        indx += temp_len

        if debug == 1:
            print "    include directories =", dir

        # read file names
        file_names = []
        i = indx
        while 1:
            # read file_name
            file_name = data[i: i + prologue["total_length"]].split('\0')[0]
            i += len(file_name) + 1

            # read dir_indx
            uleb128 = decode_uleb128(data[i: i + prologue["total_length"]], prologue["prologue_length"])
            dir_indx = uleb128[0]
            i += uleb128[1]

            # read file time
            uleb128 = decode_uleb128(data[i: i + prologue["total_length"]], prologue["prologue_length"])
            file_time = uleb128[0]
            i += uleb128[1]

            # read file length
            uleb128 = decode_uleb128(data[i: i + prologue["total_length"]], prologue["prologue_length"])
            file_len = uleb128[0]
            i += uleb128[1]

            file_names.append(copy.copy(file_name))

            if data[i] == '\0':
                break

        indx = i + 1

        if debug == 1:
            print "    file_names =", ",".join(file_names)
            print "    dir_indx =", dir_indx
            print "    time =", file_time
            print "    length =", file_len
            print ""


        # run the finite state machine

        if debug == 1:
            print "    run the finite state machine"

        base_addr = 0
        bypass_until = 0
        sm = { "address" : 0, "file" : 1, "line" : 1, "column" : 0, "is_stmt" : 0, "basic_block" : "false", "end_sequence" : "false" }

        for i in range(indx, stmt_ptr + prologue["total_length"]):
            opcode = ord(data[i])

            if debug == 1:
                print "    i =", i, "indx =", indx, "stmt_ptr =", stmt_ptr, "total_length =", prologue["total_length"]
                print "    opcode = 0x%02X" % opcode
                print "    base_addr = 0x%02X" % base_addr, "address = 0x%02X" % sm["address"], "target_addr = 0x%02X" % target_addr
                print ""

            if (bypass_until != 0) & (i < bypass_until):
                if (i + 1) == bypass_until:
                    # can disable bypass operation
                    bypass_until = 0

            elif opcode >= prologue["opcode_base"]:
                # special opcode

                # get the adjusted opcode
                adj_opcode = opcode - prologue["opcode_base"]

                # step 1: add a signed integer to the line register
                sm["line"] += prologue["line_base"] + (adj_opcode % prologue["line_range"])

                # step 2: multiply an unsigned integer by the minimum_instruction_length filed of the statement program prologue and add the result to the address register
                sm["address"] += (adj_opcode / prologue["line_range"]) * prologue["minimum_instruction_length"]

                # step 3: append a row to the matrix using the current values of the state machine registers
                if (base_addr <= target_addr) & (sm["address"] >= target_addr):
                    # found
                    result[1] = dir[dir_indx]
                    result[2] = file_names[sm["file"] - 1]
                    result[3] = sm["line"]
                    break

                # step 4: set the basic_block register to "false"
                sm["basic_block"] = "false"

            elif opcode == 0:
                # extended opcode

                uleb128 = decode_uleb128(data[i + 1], stmt_ptr + prologue["total_length"] - i)
                opcode = ord(data[i + uleb128[1] + 1])
                # enable bypass operation
                bypass_until = i + uleb128[1] + uleb128[0] + 1

                if opcode == DW_LNE_end_sequence:

                    # set end_sequence register as true
                    sm["end_sequence"] = "true"

                    # append a row to the matrix using the current vaules of the state machine registers
                    # noteXXX: cannot use "address >= target_addr" since this is the end of a sequence
                    if (base_addr <= target_addr) & (sm["address"] > target_addr):
                        # found
                        result[1] = dir[dir_indx]
                        result[2] = file_names[sm["file"] - 1]
                        result[3] = sm["line"]
                        break

                    # reset registers
                    sm = { "address" : 0, "file" : 1, "line" : 1, "column" : 0, "is_stmt" : 0, "basic_block" : "false", "end_sequence" : "false" }

                elif opcode == DW_LNE_set_address:

                    # set the address register to the relocatable address
                    sm["address"] = ord(data[i + uleb128[1] + 2])
                    sm["address"] |= ord(data[i + uleb128[1] + 3]) << 8
                    sm["address"] |= ord(data[i + uleb128[1] + 4]) << 16
                    sm["address"] |= ord(data[i + uleb128[1] + 5]) << 24
                    base_addr = sm["address"]

                elif opcode == DW_LNE_define_file:
                    pass

                else:
                    print "ERROR: unknown extended opcode"
                    return result

            else:
                # standard opcode

                if opcode == DW_LNS_copy:
                    if (base_addr <= target_addr) & (sm["address"] >= target_addr):
                        # found
                        result[1] = dir[dir_indx]
                        result[2] = file_names[sm["file"] - 1]
                        result[3] = sm["line"]
                        break
                    sm["basic_block"] = "false"

                elif opcode == DW_LNS_advance_pc:
                    leb128 = decode_uleb128(data[i + 1: stmt_ptr + prologue["total_length"]], stmt_ptr + prologue["total_length"] - i)
                    sm["address"] += leb128[0] * prologue["minimum_instruction_length"]

                    # enable bypass operation
                    bypass_until = i + leb128[1] + 1

                elif opcode == DW_LNS_advance_line:
                    leb128 = decode_leb128(data[i + 1: stmt_ptr + prologue["total_length"]], stmt_ptr + prologue["total_length"] - i)
                    sm["line"] += leb128[0]
                    # enable bypass operation
                    bypass_until = i + leb128[1] + 1

                elif opcode == DW_LNS_set_file:
                    leb128 = decode_uleb128(data[i + 1: stmt_ptr + prologue["total_length"]], stmt_ptr + prologue["total_length"] - i)
                    sm["file"] = leb128[0]
                    # enable bypass operation
                    bypass_until = i + leb128[1] + 1

                elif opcode == DW_LNS_set_column:
                    leb128 = decode_uleb128(data[i + 1: stmt_ptr + prologue["total_length"]], stmt_ptr + prologue["total_length"] - i)
                    sm["column"] = leb128[0]

                    # enable bypass operation
                    bypass_until = i + leb128[1] + 1

                elif opcode == DW_LNS_negate_stmt:
                    if sm["is_stmt"] == "true":
                        sm["is_stmt"] = "false"
                    else:
                        sm["is_stmt"] = "true"

                elif opcode == DW_LNS_set_basic_block:
                    sm["basic_block"] = "true"

                elif opcode == DW_LNS_const_add_pc:
                    sm["address"] += ((255 - prologue["opcode_base"]) / prologue["line_range"]) * prologue["minimum_instruction_length"]


                elif opcode == DW_LNS_fixed_advance_pc:
                    adv = struct.unpack("<H", data[i + 1: stmt_ptr + prologue["total_length"]])
                    sm["address"] += adv

                    # enable bypass operation
                    bypass_until = i + 3

                else:
                    print "ERROR: unknown standard opcode"
                    return result


            # skip if this statement program is not the candidate
            if sm["address"] != 0:
                if sm["address"] > target_addr:
                    break
                if (target_addr - sm["address"]) > 0x10000:
                    break

        if debug == 1:
            print ""

        """
            go to the next prologue
        """

        indx = stmt_ptr + prologue["total_length"]

        # round up to 4 byets aligned
        indx = ((indx + 4 - 1) / 4) * 4

        if result[3] != -1:
            # found
            break


    if debug == 1:
        print ""

    return result


def list_source(load_path, dir, file_name, line, debug):
    full_path = ""

    try:
        if debug == 1:
            print "    open", load_path + file_name
        f = open(load_path + file_name)
        full_path = file_name
    except IOError:
        # try to add a prefix of path
        if debug == 1:
            print "    fail to open", load_path + file_name
            print "    open", load_path + dir + file_name
        try:
            f = open(load_path + dir + file_name)
            full_path = load_path + dir + file_name
        except IOError:
            if dir == "":
                print "fail to open", load_path + file_name
            else:
                print "fail to open", load_path + file_name, "or", load_path + dir + file_name

    if full_path == "":
        return

    try:
        try:

            start_line = line - 10
            if start_line < 0:
                start_line = 0
            end_line = line + 10

            cur_line = 1
            while 1:
                source = f.readline()
                if source == "":
                    break
                if (cur_line >= start_line) & (cur_line <= end_line):
                    print "%7d" % cur_line, "  ", source[:len(source) - 1]
                cur_line += 1
                if cur_line > end_line:
                    break;

        finally:
            f.close()
    except IOError:
        print "fail to read", full_path

def lsba(argv):
    """
        define error code
    """
    er_show_help = 1  # show help
    er_invalid_arg = 2  # invalid arguments
    er_internal = 3 # internal error


    """
        get arguments

    """

    try:
        opts, args = getopt.getopt(argv, "hde:l:a:", ["elf=", "load=", "addr="])
    except getopt.GetoptError:
        usage()
        sys.exit(er_invalid_arg)

    debug = 0
    elf_path = ""
    load_path = ""
    addr = 0

    for opt, arg in opts:
        if opt == "-d":
            debug = 1
        elif opt == "-h":
            usage()
            sys.exit(er_show_help)
        elif opt in ("--elf", "-e"):
            elf_path = arg
        elif opt in ("--load", "-l"):
            load_path = arg
        elif opt in ("--addr", "-a"):
            if (arg[0:1] == "0x"):
                addr = int(arg[2:], 16)
            elif (arg[0:1] == "0X"):
                addr = int(arg[2:], 16)
            else:
                addr = int(arg, 16)

    if elf_path == "":
        usage()
        sys.exit(er_invalid_arg)

    addr = addr & 0xFFFFFFFE

    if load_path == "":
        # use MAUI directory structure by default
        (path, name) = os.path.split(elf_path)
        if path != "":
            load_path = os.path.abspath(path + os.path.sep + ".." + os.path.sep + ".." + os.path.sep)
    if len(load_path) != 0:
        if load_path[len(load_path) - 1] != os.path.sep:
            load_path += os.path.sep

    if debug == 1:
        print "load path =", load_path

    """
        parse ELF file
    """

    print "parsing", elf_path, "..."
    print ""

    try:
        f = open(elf_path, "rb")

        try:
            # result = [function_name, source_file, line_nr]
            result = [ "", "", -1 ]
            # ELF header
            elf_hdr = {}
            # section header
            sh = {}
            # section header array
            sh_tbl = []

            """
                get the ELF header
            """

            data = f.read(54)
            temp = struct.unpack("<BBBBBBBBBBBBBBBBHHLLLLLHHHHHHH", data)

            elf_hdr["ident"] = temp[0]
            elf_hdr["type"] = temp[16]
            elf_hdr["machine"] = temp[17]
            elf_hdr["version"] = temp[18]
            elf_hdr["entry"] = temp[19]
            elf_hdr["phoff"] = temp[20]
            elf_hdr["shoff"] = temp[21]
            elf_hdr["flags"] = temp[22]
            elf_hdr["ehsize"] = temp[23]
            elf_hdr["phentsize"] = temp[24]
            elf_hdr["phnum"] = temp[25]
            elf_hdr["shentsize"] = temp[26]
            elf_hdr["shnum"] = temp[27]
            elf_hdr["shstrndx"] = temp[28]

            if debug == 1:
                print "ELF header:"
                print "\n".join(["    %s = %d" % (field, value) for field, value in elf_hdr.items()])
                print "\n"


            """
                get the section header array
            """

            f.seek(elf_hdr["shoff"], 0)
            for i in range (0, elf_hdr["shnum"]):
                data = f.read(elf_hdr["shentsize"])
                temp = struct.unpack("<LLLLLLLLLL", data)
                sh["name"] = temp[0]
                sh["type"] = temp[1]
                sh["flags"] = temp[2]
                sh["addr"] = temp[3]
                sh["offset"] = temp[4]
                sh["size"] = temp[5]
                sh["link"] = temp[6]
                sh["info"] = temp[7]
                sh["addralign"] = temp[8]
                sh["entsize"] = temp[9]
                sh_tbl.append(copy.copy(sh))

            for i in range (0, elf_hdr["shnum"]):
                if debug == 1:
                    print "section header", i
                    print "\n".join(["    %s = %d" % (field, value) for field, value in sh_tbl[i].items()])
                    print ""


            """
                get the string table
            """

            f.seek(sh_tbl[elf_hdr["shstrndx"]]["offset"], 0)
            str_tbl = f.read(sh_tbl[elf_hdr["shstrndx"]]["size"])
            if debug == 1:
                print "string table:"
                print "\n".join(str_tbl.split('\0'))


            """
                get the section header for .debug_line
            """

            nr_sh = -1

            for i in range (0, elf_hdr["shnum"]):
                name = str_tbl[sh_tbl[i]["name"]: ].split('\0')
                if debug == 1:
                    print "section", i, ":", name[0]
                if name[0] == ".debug_line":
                    nr_sh = i

            if nr_sh == -1:
                sys.exit(nr_internal)

            if debug == 1:
                print ""
                print ".debug_line section:"
                print "    section", nr_sh
                print "    section header:"
                print "\n".join(["        %s = %d" % (field, value) for field, value in sh_tbl[nr_sh].items()])
                print ""


            """
                parse the .debug_line section to find source code
            """

            f.seek(sh_tbl[nr_sh]["offset"])
            data = f.read(sh_tbl[nr_sh]["size"])

            result = read_debug_line(data, sh_tbl[nr_sh]["size"], addr, debug)
            if result[3] == -1:
                print "fail to find source file for 0x%X" % addr
                print ""
            else:
                print "source file information:"
                print "    diretory =", result[1]
                print "    file name =", result[2]
                print "    line number =", result[3]
                print ""

                print "list source:"
                print ""
                list_source(load_path, result[1], result[2], result[3], debug)

        except IOError:
            print "fail to read", elf_path

        finally:
            f.close()

    except IOError:
        print "fail to open", elf_path


if __name__ == "__main__":
    lsba(sys.argv[1:])
