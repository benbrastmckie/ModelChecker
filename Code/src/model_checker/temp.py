    def print_ext_prop(prop,world,indent):
        print("{indent}|{sentence(prop)}| = {vers_fals(prop)} is {truth_val(prop, world)} in {state(world)}")
        if 'neg' in prop:
            indent =+ 1
            arg = prop[1]
            rec_print(arg,world,indent)
        if 'wedge' in prop:
            indent =+ 1
            arg_1 = prop[1]
            arg_2 = prop[2]
            rec_print(arg_1,world,indent)
            rec_print(arg_2,world,indent)
        if 'vee' in prop:
            etc
        if 'rightarrow' in prop:
            etc
        if 'leftrightarrow' in prop:
            etc

    def print_modal_prop(prop,world,indent):
        print("{indent}|{sentence(prop)}| = {vers_fals(prop)} is {truth_val(prop, world)} in {state(world)}")
        indent =+ 1
        arg = prop["prefix sentence"][1]
        for u in all_worlds:
            rec_print(arg,u,indent)
        return

    def print_cf_prop(prop,world,indent,output):
        print("{indent}|{sentence(prop)}| = {vers_fals(prop)} is {truth_val(prop, world)} in {state(world)}")
        indent =+ 1
        arg_1 = prop[1]
        arg_2 = prop[2]
        ver_arg_1 = arg_1["verifier"]
        print = True
        alt_worlds = find_alt_bits(ver_arg_1,world,indent,print) 
        print(
            f"  {self}-alternatives to {bitvec_to_substates(world, N)} = {make_set_pretty_for_print(alt_worlds)}",
            file=output,
        )
        indent =+ 1
        for u in alt_worlds:
            rec_print(arg_2,u,indent)

    def rec_print(prop, world, indent):
        operator = prop["prefix sentence"][0]
        if 'Box' in operator or 'Diamond' in operator:
            print_modal_prop(prop,world,indent)
            return
        if 'boxright' == operator:
            print_cf_prop(prop,world,indent,ouput)
            return
        print_ext_prop(prop,world,indent)

