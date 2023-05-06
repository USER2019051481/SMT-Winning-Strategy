class NormalGenerator:
    def __init__(self, domain,pwd):
        self.domain = domain
        self.transition_formula = domain.transition_formula()
        self.ending_state = [self.get_state_tuple(state) for state in domain.ending_states]
        self.constraint = self.domain.constraints
        self.p_demo = {*self.ending_state}
        self.n_demo = set()
        self.p_set = {*self.ending_state}
        self.n_set = set()
        self.not_equ_ending = False
        self.pwd = pwd


        # 令P-state不能为ending state
        for state in self.ending_state: #遍历结果状态
            for i, j in zip(list(domain.pddl2icg.values()), state):
                self.not_equ_ending = Or(self.not_equ_ending, i != j)
        # print("ffffffffffffffffffffffffffffff",self.not_equ_ending)
        self.not_equ_ending = simplify(self.not_equ_ending)
        print("P-state constraint:", self.not_equ_ending)
        print("Transition formula of %s:" % domain.name)
        print(self.transition_formula)
        print("Ending states:", *self.ending_state)
        print("Constraint:", domain.constraints)

    def get_state_tuple(self, var_dict): #转为元组
        return tuple(var_dict.values())

    def gen_eff(self, state):  #将状态放进去，state再代入v中 ，得到的是后续状态
        var_dict = dict(zip(self.domain.pddl2icg.keys(), state)) #v=2
        # print("state:\n",state)
        # print("@@@@@@@@@@@@@@@@@@@@@@@@@test4",var_dict) #{'?v1': 1, '?v2': 0}
        for action in self.domain.actions:
            # print("test4",param)
            #############
            # param_dict = list()
            #############
            param, param_set, ok = action.get_all_params(var_dict)  #得到k和l的所有取值
            # print("###################",param, param_set, ok) #(['?k', '?l'], {(1,), (1, 1)}, True)
            # print("%%%%%%%%%%%%%%%%%%%%%5",  param_set ) #[{1, 2}]
            if param_set is not None:
                param_set = list(param_set)

            # pri
            # Condition1 sat.nt("test4",var_dict) #{v1:1 , v2：1}
            if ok:
                # print("param_Set[0] = **************************",param )
                if    param is not None and  param_set[0] is not None and len(param)  == 1   :
                    # print("$$$$$$$$$$$$$$$$$$$",param)
                    if len(param_set[0]) > 0:
                        for k in param_set[0]:
                            param_dict = {param[0]: k}
                            # print("eeeeeeeeeeeeeeeeeeee",type(param_dict) ) #{'?k': 1}
                            eff_dict = action.get_eff(var_dict, param_dict)  # eff_dict = var_dict - param_dict
                            # print("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$",var_dict,param_dict) #{'?v1': 0, '?v2': 1} {'?k': 1}
                            # print("eff_dict=\n",eff_dict) #{'?v': 1}
                            if eff_dict is not None:
                                yield self.get_state_tuple(eff_dict)
                ###########################
                elif   param is not None and param_set[0] is not None and len(param) > 1 and len(param_set[0]) > 0:
                    # print("param_Set = ***************************",param,param_set)
                    param_dict = {}
                    for i in range(len(param)):
                        for k in param_set[i]:
                            param_dict[param[i]] = k
                            # print("$$$$$$$$$$$$$$$$$$$$$",i,param_dict)
                    eff_dict = action.get_eff(var_dict,param_dict)
                    if eff_dict is not None:
                        yield  self.get_state_tuple(eff_dict)

                ############################



                elif param is not None:
                    # print("param = ***********************",param)
                    param_dict = {}
                    for i in range(len(param)):
                        param_dict[param[i]] =  0
                    # print("test4",param_dict)
                    eff_dict = action.get_eff(var_dict, param_dict)
                    if eff_dict is not None:
                        yield self.get_state_tuple(eff_dict)

    def check_np(self, state):
        if state in self.p_demo:  #p_demo，是P位置
            return False  # It is a P state
        elif state in self.n_demo:# n_demo，是N位置
            return True  # It is a N state
        for eff_tuple in self.gen_eff(state): #找state的后续状态
            if not self.check_np(eff_tuple):  # exits an eff that is a P state ，找到N位置，递归继续找后续状态
                self.n_demo.add(state) #得到的是N位置的值
                return True #返回标志
        self.p_demo.add(state)   #找到了P位置，返回P位置的标志
        return False

    def generate_formula(self, w,idx ): ##改动！！！！！
        # print("!!!!!!!!!!!!!!!!!!!!!!!!!111111111111111!!!!!!!!!!",w)
        if (idx > 20):
            idx = 0

        print("\n\nsize:", tmp_size[idx])

        # print("sfadsafasdfasf",w)
        self.formula_template = FormulaTemplate(list(self.domain.pddl2icg.values()),w,*tmp_size[idx],self.pwd)

        eff_var = list(self.domain.eff_mapper.values())
        # print("eff_var:\n",eff_var)


        def con1(nf, a_nf):  # N-state的约束
            return Implies(nf, Exists(eff_var, And(self.transition_formula, Not(a_nf)))) #存在V0 ， 后继状态有P位置

        def con2(nf, a_nf):  # P-state的约束
            return Implies(And(self.not_equ_ending, Not(nf)), ForAll(eff_var, Implies(self.transition_formula, a_nf)))

        for state in self.p_set:
            self.formula_template.add(state, False)
        for state in self.n_set:
            self.formula_template.add(state, True)

        # print("1111111111111111111111111111111111111111111111111")

        if self.formula_template.check() == unsat:
            print("###unsat, extending...")
            w = w + 1
            idx = idx + 1
            return self.generate_formula(w  ,idx  )


        while True:
            print("\nSP:", self.p_set)
            print("SN:", self.n_set)
            # nf = self.formula_template.formula_model()
            # a_nf = self.formula_template.formula_model(*eff_var)
            #############################################33
            nf = self.formula_template.formula_model1(self.n_set,self.p_set)
            a_nf = self.formula_template.formula_model1(self.n_set,self.p_set,*eff_var)
            #############################################3333
            print("N-formula: \n", nf)

            s1 = Solver()
            s1.set("timeout", 600000)
            s1.add(self.constraint, Not(con1(nf, a_nf)))
            # print(self.constraint,"222222222222222222222222233333333333333333")
            flag = 0 #标记此轮有没有例子放入后台
            if s1.check() == sat:
                model = s1.model()

                # print(example,"11111111111111111111111111111111")
                #########################################################3
                pre =None
                while flag == 0 :
                    print(pre,"############################################################33")
                    if pre != None:
                        if(len(pre)==1):
                            s1.add(self.formula_template.vi[0] != pre[0])
                        elif(len(pre)==2):
                            s1.add(self.formula_template.vi[0] != pre[0])
                            s1.add(self.formula_template.vi[1] != pre[1])
                        elif(len(pre)==3):
                            s1.add(self.formula_template.vi[0] != pre[0])
                            s1.add(self.formula_template.vi[1] != pre[1])
                            s1.add(self.formula_template.vi[2] != pre[2])

                    if s1.check() == sat:
                        model = s1.model()
                    # print(s1,"!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                    example = [model[self.formula_template.vi[i]].as_long()
                               if model[self.formula_template.vi[i]] is not None
                               else 0 for i in range(self.formula_template.n)]

                    example = tuple(example)
                    pre = example
                    if self.check_np(example):  #N
                        if example in self.n_set:
                            for eff in self.gen_eff(example):
                                if self.check_np(eff): #N
                                    if eff in self.n_set:
                                        continue
                                    else:
                                        print("Find a counter n_eff", eff)
                                        flag = 1
                                        self.formula_template.add(eff,True)
                                        self.n_set.add(eff)
                                        break
                                else: #P
                                    if eff in self.p_set:
                                        continue
                                    else:
                                        print("Find a counter p_eff",eff)
                                        flag = 1
                                        self.formula_template.add(eff,False)
                                        self.p_set.add(eff)
                                        break
                        else: #N
                            print("Find a counter example", example)
                            flag = 1
                            self.formula_template.add(example,True)
                            self.n_set.add(example)

                    else: #P
                        if example in self.p_set:
                            for eff in self.gen_eff(example):
                                if self.check_np(eff): #N
                                    if eff in self.n_set:
                                        continue
                                    else:
                                        print("Find a counter n_eff", eff)
                                        flag = 1
                                        self.formula_template.add(eff,True)
                                        self.n_set.add(eff)
                                        break
                                else: #P
                                    if eff in self.p_set:
                                        continue
                                    else:
                                        print("Find a counter p_eff",eff)
                                        flag = 1
                                        self.formula_template.add(eff,False)
                                        self.p_set.add(eff)
                                        break
                        else:
                            print("Find a counter example", example)
                            flag = 1
                            self.formula_template.add(example, False)
                            self.p_set.add(example)

                #####################################################################3

            else:
                print("Condition1 sat.")

                s2 = Solver()
                s2.set("timeout", 600000)
                s2.add(self.constraint, Not(con2(nf, a_nf)))
                if s2.check() == sat:
                    model = s2.model()
                    flag1 = 0
                    pre = None
                    while flag1 == 0:
                        if pre != None:
                            # print(pre, len(pre),pre[0], "333333333333333333333333")
                            # print(s2)
                            if (len(pre) == 1):
                                s2.add(self.formula_template.vi[0] != pre[0])
                            elif (len(pre) == 2):
                                s2.add(self.formula_template.vi[0] != pre[0])
                                s2.add(self.formula_template.vi[1] != pre[1])
                            elif (len(pre) == 3):
                                s2.add(self.formula_template.vi[0] != pre[0])
                                s2.add(self.formula_template.vi[1] != pre[1])
                                s2.add(self.formula_template.vi[2] != pre[2])
                        ################################3
                        if s2.check() == sat:
                            model = s2.model()
                       ######################################33
                        example = [model[self.formula_template.vi[i]].as_long()
                                   if model[self.formula_template.vi[i]] is not None
                                   else 0 for i in range(self.formula_template.n)]
                        example = tuple(example)
                        # print(example,"2222222222222222222222222222222222")
                        pre = example
                    #######################################################################3


                        if self.check_np(example):  # N
                            if example in self.n_set:
                                for eff in self.gen_eff(example):
                                    if self.check_np(eff):  # N
                                        if eff in self.n_set:
                                            continue
                                        else:
                                            print("Find a counter n_eff", eff)
                                            flag1= 1
                                            self.formula_template.add(eff, True)
                                            self.n_set.add(eff)
                                            break
                                    else:  # P
                                        if eff in self.p_set:
                                            continue
                                        else:
                                            print("Find a counter p_eff", eff)
                                            flag1 = 1
                                            self.formula_template.add(eff, False)
                                            self.p_set.add(eff)
                                            break
                            else:  # N
                                print("Find a counter example", example)
                                flag1= 1
                                self.formula_template.add(example, True)
                                self.n_set.add(example)

                        else:  # P
                            if example in self.p_set:
                                for eff in self.gen_eff(example):
                                    if self.check_np(eff):  # N
                                        if eff in self.n_set:
                                            continue
                                        else:
                                            print("Find a counter n_eff", eff)
                                            flag1 = 1
                                            self.formula_template.add(eff, True)
                                            self.n_set.add(eff)
                                            break
                                    else:  # P
                                        if eff in self.p_set:
                                            continue
                                        else:
                                            print("Find a counter p_eff", eff)
                                            flag1 = 1
                                            self.formula_template.add(eff, False)
                                            self.p_set.add(eff)
                                            break
                            else:
                                print("Find a counter example", example)
                                flag1 = 1
                                self.formula_template.add(example, False)
                                self.p_set.add(example)
                ################################################################

                else:
                    print("condition2 sat.")
                    break
            ###############
            global g_nf
            # self.formula_template.add1(Not(g_nf))
            # g_nf = nf
           # ####################

            print('generating formula...')
            w = w + 1
            # print("fsadfadfadsfadsfa",w)
            check = self.formula_template.check()
            if flag == 0 :
                # w = w + 1
                idx = idx + 1
                return self.generate_formula(w ,idx)
            # print("ccccccccccccccccccccccccccccccccccc",check)
            else:
                if check == unknown:
                    raise RuntimeError("z3 solver running out of time")
                elif check == unsat:
                    print('###unsat, extending...')
                    w = w - 1
                    idx = idx + 1
                    return self.generate_formula(w ,idx )
                else:
                    if len(self.p_set) > 4 * len(self.n_set):
                        print('###extending...')
                        for s in self.n_demo:
                            if s not in self.n_set:
                                self.n_set.add(s)
                                if len(self.p_set) < 2 * len(self.n_set):
                                    break
                        # w = w + 1
                        idx = idx + 1
                        return self.generate_formula(w ,idx )
                    if len(self.n_set) > 4 * len(self.p_set):
                        print('###extending...')
                        for s in self.p_demo:
                            if s not in self.p_set:
                                self.p_set.add(s)
                                if len(self.n_set) < 2 * len(self.p_set):
                                    break
                    # w = w + 1
                    idx = idx + 1
                    return self.generate_formula(w ,idx )



        return self.formula_template
        # return self.formula_template,nf

    def gen_example_of_cover(self, cover, demo):
        s = Solver()
        s.add(cover)
        s.add(self.domain.constraints)
        vi = list(self.domain.pddl2icg.values())
        for state in demo:
            s.add(*[vi[i] != state[i] for i in range(len(vi))])
        if s.check() == sat:
            model = s.model()
            example = [model[vi[i]].as_long()
                       if model[vi[i]] is not None else 0 for i in range(len(vi))]
            example = tuple(example)
            demo[example] = []

    def gen_eff2(self, state, action):
        var_dict = dict(zip(self.domain.pddl2icg.keys(), state))
        # print("var_dict = !!!!!!!!!!@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@",var_dict)
        param, param_set, ok = action.get_all_params(var_dict)
        # print("#######################################param =  param_set  , ok ",param , param_set,ok)
        #['?k', '?k1'] {(1,), (1, 1)} True
        if ok:
            if   param != None and len(param_set[0]) > 0 :
                if len(param)==1 and param_set[0] is not None:
                    for k in param_set[0]:
                        param_dict = {param[0]: k}
                        eff_dict = action.get_eff(var_dict, param_dict)
                        # print("eff_dict = ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^",eff_dict)
                        if eff_dict is not None:
                            res = self.get_state_tuple(eff_dict)
                            if not self.check_np(res):
                                # print("k , action.name , res )))))))))))))))))))))))",k , action.name,res)
                                yield k, action.name, res
                elif param_set[0] is not None:

                        # print("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%多于俩参数！！还没写",param,param_set)
                        param_dict = {}
                        for i in range(len(param)):
                            for k in param_set[i]:
                                param_dict[param[i]] = k
                                # print("k = ***************************",k)
                        # print("var_Dcit , param_dict = &&&&&&&&&&&&&&&&&&&&&&&&&&&&",var_dict , param_dict)
                        eff_dict = action.get_eff(var_dict , param_dict)
                        # print("eff_dict = &&&&&&&&&&&&&&&&&&&&&&&&",eff_dict)
                        if eff_dict is not None:
                            # print("afdasfa")
                            res = self.get_state_tuple(eff_dict)
                            if not self.check_np(res):
                                # print("#########################k ,action.name , res",k , action.name , res)
                                yield k , action.name , res
            else:
                param_dict = {}
                for i in range(len(param)):
                    param_dict[param[i]] = 0
                eff_dict = action.get_eff(var_dict, param_dict)
                if eff_dict is not None:
                    res = self.get_state_tuple(eff_dict)
                    if not self.check_np(res):
                        yield 0, action.name, res

    def combination_of_demo(self, state_list, demo, tmp, res):
        if len(state_list) == 0:
            res.append(list(tmp))
            return
        state = []
        state.extend(state_list[0])
        for b in demo[state_list[0]]:
            state.append(b)
            tmp.append(list(state))
            self.combination_of_demo(state_list[1:], demo, tmp, res)
            tmp.pop()
            state.pop()

    def generate_param(self, exam_set):
        rqu_template = EquTemplate(len(self.domain.pddl2icg))
        for vec in exam_set:
            rqu_template.add(vec)
        if rqu_template.check() == sat:
            return rqu_template.solve_model()
        return None

    def generate_strategy(self):
        # print(self.formula_template,"###################################3333")
        model = self.formula_template.refine_model()
        refiner = Refiner(list(self.domain.pddl2icg.values()))
        # print(model ,  "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
        refiner_model = refiner.refine(model, self.domain.feasible_region)
        print('*' * 50)
        print('refined model:', refiner_model)

        strategies = []
        find = [False for _ in refiner_model]
        for cover_idx, cover_list in enumerate(refiner_model): #cover_idx 是余数
            # print(cover_list,"!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11")
            cover = simplify(And(*cover_list))
            # cover =  cover_list
            print("cover = ",cover )
            print('-' * 50, "\ncover:", cover)  #cover: v0%7 == 1
            for action in self.domain.actions:
                # print("action =~~~~~~~~~~~~~~~~~~~~~~~~~~~~~`` ",action )
                flag, demo = False, dict()
                # print("demo = ******************************",demo)
                for i in range(5):  # 生成5个用例
                    self.gen_example_of_cover(cover, demo)
                state_list = list(demo.keys())
                # print("state_list = *********************************",state_list)
                # #[(1,), (8,), (15,), (22,), (29,)]
                for state in state_list:
                    params = [param[0] for param in self.gen_eff2(state, action)]
                    # print("params = wwww!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!",params) #[2, 4, 6]
                    if len(params) > 0:
                        demo[state] = [k for k in params]
                        # print("demo[state] , state",demo[state] , state)
                    else:
                        flag = True
                        break
                if flag:  # 找不到后继状态中的P状态
                    continue

                eff_var = list(self.domain.eff_mapper.values())
                # print("eff_var = ****************************",eff_var) #[w0]
                while True:
                    print(action.name, demo)
                    state_list = list(demo.keys())
                    comb_list = []  # 当前action下可能的所有情况

                    self.combination_of_demo(state_list, demo, [], comb_list)
                    # print("con_list", comb_list)
                    while len(comb_list) > 0:
                        # for example_set in comb_list:
                        example_set = comb_list[0]
                        # print('example:***************************************', comb_list)
                        comb_list = comb_list[1:]
                        param_expr = self.generate_param(example_set)
                        # print("param_expr",param_expr)
                        if param_expr is None:
                            continue

                        print("param of action:", param_expr)
                        tf = action.trans_formula()
                        wf = self.formula_template.formula_model1([],[],*eff_var)
                        const = simplify(Implies(cover, ForAll(eff_var, Implies(tf, Not(wf)))))
                        free_p = list(action.params_mapper.values())[0]  # 动作的参数
                        s = Solver()
                        s.add(self.domain.constraints, free_p == param_expr, Not(const))
                        if s.check() == sat:
                            model = s.model()
                            example = [model[self.formula_template.vi[i]].as_long()
                                       if model[self.formula_template.vi[i]] is not None
                                       else 0 for i in range(self.formula_template.n)]
                            example = tuple(example)
                            print(model)
                            print("find a counterexample:", example)
                            params = [param[0] for param in self.gen_eff2(example, action)]
                            if len(params) > 0:
                                demo[example] = [k for k in params]
                                need_to_append_list = [[*example, k] for k in params]
                                k = len(comb_list)
                                for ntal in need_to_append_list:
                                    comb_list.append([*example_set, ntal])
                                while k > 0:
                                    example_set = comb_list[0]
                                    comb_list = comb_list[1:]
                                    k -= 1
                                    for ntal in need_to_append_list:
                                               comb_list.append([*example_set, ntal])
                            else:
                                break
                        else:
                            strategies.append((cover, action.name, param_expr))
                            find[cover_idx] = True
                            flag = True
                            break  # break for loop
                    if flag:
                        break  # break while loop
                if flag:
                    break  # break action loop
                # 遍历完了action也没有找到策略

        failed_cover_list = [simplify(And(*cover_list))
                             for i, cover_list in enumerate(refiner_model)
                             if not find[i]]
        if (len(failed_cover_list)) > 0:
            print('failed cover', failed_cover_list)
        return strategies

