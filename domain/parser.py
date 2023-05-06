import re

from z3 import Int, And, Or, Exists, simplify
from SMT.smt.domain.utils.split import split
from SMT.smt.domain.utils.analyse_snt import analyse_snt_z3
from SMT.smt.domain.action import Action


# PDDL文件解析器
class PDDLParser:
    def __init__(self, pddl_pwd):
        self.pddl2icg = {}
        self.eff_mapper = {}
        self.constant_mapper = {}
        # self.variables = []
        self.ending_states = []
        self.constraints = None
        self.actions = []
        self.feasible_region = None


        lines = []
        for line in open(pddl_pwd):
            lines.append(line.strip())
        pddl_ln = ' '.join(lines)
        pddl_tasks = split(pddl_ln)

        print("Preliminary analyse:")
        for task in pddl_tasks:
            print(task)
        print("/" * 50)

        task_dict = {"action": []}
        for task in pddl_tasks:
            if task[0][0] == ':':
                key = task[0][1:]
                if key == 'action':
                    task_dict[key].append(task[1:])
                    # print("ttttttttttttttttttttttttttttask_dict = ",task_dict)
                else:
                    task_dict[key] = task[1:]
                    # print("ttttttttttttttttttttttttttttask1111_dict = ",task_dict)
            else:
                if task[0] == 'domain':
                    self.name = task[1]
        print( self.name)

        #####找到名字中的参数
        number = re.findall(r"[-+]?\d*\.\d+|\d+",self.name)

        # print("找到的常数为@@@@@",type(number))

        #####
        # print("task——dict = ::::::::::::::::::::::::::::::",task_dict)

        print("Turning into task_dict:")
        for k, v in task_dict.items():
            print("%s: %s" % (k, v))
        print("/" * 100)

        if "constants" in task_dict:
            print("Analysing constants:")
            self._analyse_constants(task_dict["constants"])
            print(self.constant_mapper)
            self._replace_constant(task_dict["tercondition"])
            self._replace_constant(task_dict["constraint"])
            self._replace_constant(task_dict["action"])
            print("/" * 50)

        print("Analysing objects:")
        self._analyse_objects(task_dict["objects"])
        self.eff_mapper = {k: Int("w%d" % i) for i, k in enumerate(self.pddl2icg)}
        print("variable mapper(pddl2icg):", self.pddl2icg)
        # print("variables:", self.variables)
        print("/" * 50)

        print("Analysing ending states:")
        states = self._analyse_tercondition(task_dict["tercondition"][0])
        # print("states   @@@@@@@@@@@@@@@@@@@@@@@@@2" , states) #{'?v1': 3, '?v2': 3, '?v3': 3}
        if type(states) == list:
            self.ending_states.extend(states)
        else:
            self.ending_states.append(states)
        print(self.ending_states)
        print("/" * 50)

        print("Analysing feasible region:")
        # print("!!!!!!!!!!!!self._feasible_region(task_dict)=", task_dict)
        self.feasible_region = self._feasible_region(task_dict["constraint"][0])
       # self.feasible_region = self.feasible_region(task_dict["feasible"][0])
        print(self.feasible_region)
        print("/" * 50)


        print("Analysing constraint:")
        self.constraints = self._analyse_constraint(task_dict["constraint"][0])
        print(self.constraints)
        print("/" * 50)

        print("Analysing actions:")
        self.actions.extend(self._analyse_action(task_dict["action"]))
        print("/" * 100)






    def _analyse_constants(self, arr):
        self.constant_mapper = {arr[i]: arr[i + 1] for i in range(0, len(arr), 2)}

    def _replace_constant(self, arr):
        for i, elem in enumerate(arr):
            if type(elem) == list :
                self._replace_constant(elem)
            elif elem in self.constant_mapper:
                    arr[i] = self.constant_mapper[elem]

    def _analyse_objects(self, arr):
        # 解析PDDL中的变量，将其转化为Z3的变量，用列表按序存储
        for i, pddl_var in enumerate(arr):
            icg_var = Int("v%d" % i)
            # self.variables.append(icg_var)
            self.pddl2icg[pddl_var] = icg_var

    def _analyse_tercondition(self, arr):

        ans = list()
        # print(arr[0]=="=")
        if arr[0] == "=" and arr[1][0] == "+":
            ending_state_mapper = dict()
            for i in range(int(arr[2])):
                ending_state_mapper[arr[1][1]] = i
                ending_state_mapper[arr[1][2]] = int(arr[2]) - i
                ans.append(ending_state_mapper)
            return ans

        if arr[0] == '=':
            ans.append({arr[1]: int(arr[2])})
            return ans
        if arr[0] == '<':
            for i in range(int(arr[2])):
                ans.append({arr[1]: i})
                print(ans)
            return ans

        if arr[0] ==">" and arr[2][0] == "+" and arr[2][2][0] =="+":
            # print("#######################33")
            #将P位置减少，因为太多的话，程序跑不动
            if int(arr[1]) > 2:
                arr[1] = 2
            for i in range(int(arr[1])):
                for j in range(int(arr[1]) - i +1):
                    for k in range(int(arr[1])-i-j+1):
                        ending_state_mapper = dict()
                        ending_state_mapper[arr[2][1]] = i
                        ending_state_mapper[arr[2][2][1]] = j
                        ending_state_mapper[arr[2][2][2]] = k
                        ans.append(ending_state_mapper)
            return ans

        if arr[0] == '>=':
            for i in range(5):
                ans.append(({arr[1] : i+arr[2]}))
            return ans
        if arr[0] == 'or':
            num = 0
            # print(len(arr))
            # print("##################@@@@@@@@@@@@@@@@@@@@@2"+arr[1][0]+"##"+arr[2][0]+"3##"+arr[3][0])
            if arr[1][0] == "and" and arr[2][0] == "and" and arr[3][0] =="and":
                for i in range(1,4):
                    if arr[i][1][0] == ">" and arr[i][2][0] =="=" and arr[i][3][0] =="=":
                        for i in range(int(arr[i][1][2])+1 , int(arr[i][1][2])+4):
                            ending_state_mapper = dict()
                            ending_state_mapper[arr[i][1][1]] = i
                            ending_state_mapper[arr[i][2][1]] = int(arr[i][1][2])
                            ending_state_mapper[arr[i][3][1]] = int(arr[i][3][2])
                            ans.append(ending_state_mapper)
                return ans

            for i in range(1,len(arr)):
                # print(i)
                for k in range(3):
                    ending_state_mapper = dict()

                    for j in range(1,len(arr)):
                        if i == j and arr[i][0] == '=':
                            ending_state_mapper[arr[i][1]] = int(arr[i][2])
                        if i != j:
                            ending_state_mapper[arr[j][1]] = k
                    ans.append(ending_state_mapper)
            # print(ans)
            return ans
            # for state in arr[1:]:
            #     if state[0] == '=':
            #         ending_state_mapper[state[1]] = int(state[2])


        flag = 0
        # assert arr[0] == 'and'
        if arr[0] == 'and':
            ending_state_mapper = dict()
            # print("!!!!!!!!!!!!arr[1:]=",arr[1:])
            for state in arr[1:]:
                if state[0] == '=':
                    print("state=",state)
                    ending_state_mapper[state[1]] = int(state[2])
                    flag = 1

                else:
                    flag = 0
                    break
            if flag :
                ans.append(ending_state_mapper)
                # print("ending_State_mapper = @@@@@@@@@@@@@@@",[ending_state_mapper])

            small = list()
            Sma = list()
            for sma in arr[1:]:
                a = int(sma[2])
                small.append(a)  #存储数据
                Sma.append(sma[0]) #存储符号
            # print(small) #[0,1]
            lenSmall = len(small)
            # print("#############################",lenSmall)
            if lenSmall == 4:
                if Sma[0] == "=" and Sma[1] == "=" and Sma[2] == ">=" and Sma[3] == "<=":
                    if arr[3][1] == arr[4][1]:
                        for i in range(small[2] ,small[3]+1):
                            ending_state_mapper[arr[1][1]] = small[0]
                            ending_state_mapper[arr[2][1]] = small[1]
                            ending_state_mapper[arr[3][1]] = i
                            ans.append(ending_state_mapper)
            if lenSmall == 3:
                for i in range(1,small[0]):
                    for j in range(1,small[1]):
                        for k in range(1,small[2]) :
                            ending_state_mapper = {}
                            ending_state_mapper[arr[1][1]] = i
                            ending_state_mapper[arr[2][1]] = j
                            ending_state_mapper[arr[3][1]] = k
                            ans.append(ending_state_mapper)
            elif lenSmall == 2:
                if Sma[0] == "=" and Sma[1] =="=":
                    for i in range(small[0]):
                        for j in range(small[1]):
                            ending_state_mapper = {}
                            ending_state_mapper[arr[1][1]] = i
                            ending_state_mapper[arr[2][1]] = j
                            ans.append(ending_state_mapper)
                            print(ending_state_mapper)
                elif Sma[0] == ">=" and Sma[1] == "<" :
                    # for i in range(5):
                    #     ans.append(({arr[1][1]: i + small[0]}))
                    for i in range(3):
                        for j in range(small[1]):
                            ending_state_mapper[arr[1][1]] = i + small[0]
                            ending_state_mapper[arr[2][1]] = j
                        ans.append(ending_state_mapper)



                    #写大于等于的情况和小于等于的情况#
                # ！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！
            # print("@@@@@@@@@@@@@@@@@@@@@@@@222",ans)
            return ans

    def _analyse_constraint(self, word_list):
        def mapper1(key):
            if key in self.pddl2icg:
                return self.pddl2icg[key]
            else:
                return int(key)

        def mapper2(key):
            if key in self.eff_mapper:
                return self.eff_mapper[key]
            else:
                return int(key)

        const = And(analyse_snt_z3(word_list, mapper1), analyse_snt_z3(word_list, mapper2))
        return simplify(const)

    def _analyse_action(self, action_list):
        return [Action(snt, self.pddl2icg, self.eff_mapper) for snt in action_list]

    def _feasible_region(self, word_list):
        def mapper(key):
            # print("key = ****************************",key)
            if key in self.pddl2icg:
                print("self.pddl2icg",self.pddl2icg[key])
                return self.pddl2icg[key]
            else:
                # print("key",key)
                return  int(key)

        return analyse_snt_z3(word_list, mapper)

    def transition_formula(self):
        # print("!!!!!!!!!!!!!!!!!!!!!!!!!!!111111111111111111111111111111111111111111")
        trans = False
        for act in self.actions:
            trans = Or(trans, Exists(list(act.params_mapper.values()), act.trans_formula()))
            print("trans:\n",trans)
        return simplify(trans)


if __name__ == '__main__':
    i1 = PDDLParser('pddl/1.Sub/1.1 Take-away/Take-away-2.pddl')
    print(i1.transition_formula())

    var_dict = {"?v1": 5, "?v2": 6}
    param_dict = {"?k": 2}
    print(var_dict, i1.actions[0].get_eff(var_dict, param_dict), i1.actions[0].get_all_params(var_dict))
    print(var_dict, i1.actions[1].get_eff(var_dict, param_dict), i1.actions[1].get_all_params(var_dict))

    var_dict = {"?v1": 5, "?v2": 2}
    param_dict = {"?k": 4}
    print(var_dict, i1.actions[0].get_eff(var_dict, param_dict), i1.actions[0].get_all_params(var_dict))
    print(var_dict, i1.actions[1].get_eff(var_dict, param_dict), i1.actions[1].get_all_params(var_dict))


##########################3
