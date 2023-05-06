
import random
import re

from z3 import *
from SMT.smt.domain.parser import PDDLParser
from SMT.smt.domain.utils.split import split


def combine(iter):

    tmp_list = [i for i in iter]
    res = tmp_list[0]
    for i in tmp_list[1:]:
        res += i
    return res


def co_prime(num1, num2):
    for num in range(2, min(num1, num2) + 1):
        if num1 % num == 0 and num2 % num == 0:
            return False
    return True


def gcd(*nums):
    min_num = 1 << 32
    for num in nums:
        if num != 0:
            min_num = min(min_num, abs(num))
    for i in range(min_num, 1, -1):
        flag = True
        for num in nums:
            if num % i != 0:
                flag = False
                break
        if flag:
            return i
    return 1


class FormulaTemplate:
    def __init__(self, vi, w, k, h, m, pwd ,timeout=3000000  ):  ####加了w
        self.k = k  # amount of clause 多少个子句
        self.h = h  # number of inequality  第一类不等式数量上限
        self.m = m  # number of mode number  第二类不等式数量上限

        self.w = w

        self.vi = vi
        # print("vi   ",self.vi)
        n = len(vi)
        self.n = n
        self.aeij = [[Int('ae' + str(i) + str(j)) for j in range(n)] for i in range(h)]
        self.bi = [Int('b' + str(i)) for i in range(h)]
        self.amij = [[Int('am' + str(i) + str(j)) for j in range(n)] for i in range(m)]
        self.ei = [Int('e' + str(i)) for i in range(m)]  ##改成定值 ， 写一个函数，从2开始一个个试？？？？（还没实现）
        self.ci = [Int('c' + str(i)) for i in range(m)]
        self.heij = [[Bool('h_e' + str(j) + str(i)) for i in range(h)] for j in range(k)]
        self.hgeij = [[Bool('h_ge' + str(j) + str(i)) for i in range(h)] for j in range(k)]
        self.hleij = [[Bool('h_le' + str(j) + str(i)) for i in range(h)] for j in range(k)]
        self.tij = [[Bool('t' + str(j) + str(i)) for i in range(m)] for j in range(k)]
        self.ntij = [[Bool('nt' + str(j) + str(i)) for i in range(m)] for j in range(k)]
        self.s = Solver()

        self.pwd = pwd




        for i in range(h):
            # 不等式系数ae_ij不能全部为0
            self.s.add(Or(*[a > 0 for a in self.aeij[i]]))
            for j in range(i + 1, h):
                self.s.add(Or(*[self.aeij[i][w] != self.aeij[j][w] for w in range(n)]))
        for i in range(m):
            # 模等式的系数am_ij不能全部小于等于0
            self.s.add(Or(*[am > 0 for am in self.amij[i]]))
            # 模等式的系数am_ij不能大于模e
            self.s.add(*[And(0 <= am, am < self.ei[i]) for am in self.amij[i]])
            # for j in range(i + 1, m):
            #     self.s.add(Or(self.ei[i] != self.ei[j],
            #         *[self.amij[i][w] != self.amij[j][w] for w in range(n)]))
        # 余数c_i必须小于模e
        self.s.add(*[And(self.ei[i] > self.ci[i], self.ci[i] >= 0) for i in range(m)])
        # 模必须大于等于2，并且小于一定范围
        self.s.add(*[And(e <= 20 * m, e >= 2) for e in self.ei])
        for i in range(k):
            # 判断条件一定有一个是False，避免逻辑出现False
            for j in range(i + 1, k):
                all_true = [And(self.heij[i][w], self.hgeij[i][w], self.hleij[i][w]) for w in range(h)]
                all_true.extend([And(self.tij[i][w], self.ntij[i][w]) for w in range(m)])
                struct_const = [Or(self.heij[i][w] != self.heij[j][w],
                                   self.hgeij[i][w] != self.hgeij[j][w],
                                   self.hleij[i][w] != self.hleij[j][w]) for w in range(h)]
                struct_const.extend([Or(self.tij[i][w] != self.tij[j][w],
                                        self.ntij[i][w] != self.ntij[j][w]) for w in range(m)])

                self.s.add(Or(*struct_const, *all_true))

        self.s.set("timeout", timeout)

    def findE(self,pddl_pwd):
        lines = []
        for line in open(pddl_pwd):
            lines.append(line.strip())
        pddl_ln = ' '.join(lines)
        pddl_tasks = split(pddl_ln)

        # print("Preliminary analyse:")
        # for task in pddl_tasks:
            # print(task)
        # print("/" * 50)

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
        print(self.name)

        #####找到名字中的参数
        number = re.findall(r"[-+]?\d*\.\d+|\d+", self.name)
        # print("找到的常数为@@@@", number)
        return number
        #####

    def add(self, example, label):
        self.s.add(self.encoding(example, label))


    def add1(self,code):
        self.s.add(code)

    def check(self):
        check = self.s.check()
        if check == sat:
            self.solve_model()
        return check

    def W_size(m):
        return m+2



    def encoding(self, example, label):
        Equ = [combine(example[j] * self.aeij[i][j] for j in range(self.n)) != self.bi[i] for i in range(self.h)]
        Ge = [combine(example[j] * self.aeij[i][j] for j in range(self.n)) >= self.bi[i] for i in range(self.h)]
        Le = [combine(example[j] * self.aeij[i][j] for j in range(self.n)) <= self.bi[i] for i in range(self.h)]
        # print( self.k , self.h,self.m,self.n,example,self.amij,self.ci,self.ei)
        Me = [combine(example[j] * self.amij[i][j] for j in range(self.n)) % self.ei[i] == self.ci[i] for i in
              range(self.m)]

        Tk = []
        for k in range(self.k):
            clause = []
            clause.extend([Implies(self.heij[k][h], Equ[h]) for h in range(self.h)])
            clause.extend([Implies(self.hgeij[k][h], Ge[h]) for h in range(self.h)])
            clause.extend([Implies(self.hleij[k][h], Le[h]) for h in range(self.h)])
            clause.extend([Implies(self.tij[k][m], Me[m]) for m in range(self.m)])
            clause.extend([Implies(self.ntij[k][m], Not(Me[m])) for m in range(self.m)])
            Tk.append(And(*clause))
        # print("Or(*Tk) , label=\n",Or(*Tk),label)
        return Or(*Tk) == label




    def solve_model(self):  #求出取值  ####加了w
        model = self.s.model()
        self.M = [[model[self.amij[i][j]].as_long() if model[self.amij[i][j]] is not None else 0
                   for j in range(self.n)]
                  for i in range(self.m)]
        # print("self.M",self.M)
        for i in range(self.m):
            len1 = len(self.findE(self.pwd))
            # print("asfadsfas!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!1dfas",self.m)
            # print(self.w,"sadfasdfadfadsfasdfadsfasdf")
            if(self.w < 5) :
                self.ei[i] = self.w + 2
            elif(self.w<10):
                # print(self.w , i)
                self.ei[i] = int(self.findE(self.pwd)[len1-1])  + self.w-4
            elif(self.w<20):
                self.ei[i] = self.w + 2 -9
            else:
                self.ei[i] = int(self.findE(self.pwd)[len1 - 1]) + self.w - 19

            # print(self.ei[i],"!!!!!!!!!!!!!!!!!!!!!!!!!1")
        self.E = [self.ei[i] for i in range(self.m)]
        # print("eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",self.w,self.E)        ####


        self.C = [model[self.ci[i]].as_long() if model[self.ci[i]] is not None else 0 for i in range(self.m)]
        self.A = [[model[self.aeij[i][j]].as_long() if model[self.aeij[i][j]] is not None else 0
                   for j in range(self.n)]
                  for i in range(self.h)]

        # print("self.A",self.A)
        self.B = [model[self.bi[i]].as_long() if model[self.bi[i]] is not None else 0 for i in range(self.h)]
        self.He = [
            [bool(model[self.heij[i][j]]) if model[self.heij[i][j]] is not None else False
             for j in range(self.h)]
            for i in range(self.k)
        ]
        self.Hge = [
            [bool(model[self.hgeij[i][j]]) if model[self.hgeij[i][j]] is not None else False
             for j in range(self.h)]
            for i in range(self.k)
        ]
        self.Hle = [
            [bool(model[self.hleij[i][j]]) if model[self.hleij[i][j]] is not None else False
             for j in range(self.h)]
            for i in range(self.k)
        ]
        self.T = [
            [bool(model[self.tij[i][j]]) if model[self.tij[i][j]] is not None else False
             for j in range(self.m)]
            for i in range(self.k)
        ]
        self.Nt = [
            [bool(model[self.ntij[i][j]]) if model[self.ntij[i][j]] is not None else False
             for j in range(self.m)]
            for i in range(self.k)
        ]
        for i in range(self.m):
            flag = True # 判断是否全部系数都相等
            pix = -1
            for am in self.M[i]:
                if pix == -1:
                    if am != 0:
                        pix = am
                elif am != 0 and am != pix:
                    flag = False
                    break
        #     if flag: # 系数全部相同
        #         if self.C[i] == 0:
        #             # if co_prime(pix, self.E[i]):
        #             #     for j in range(self.n):
        #             #         if self.M[i][j] != 0:
        #             #             self.M[i][j] = 1
        #             # else:
        #             #     div = gcd(pix, self.E[i])
        #             #     self.E[i] /= div
        #             #     for j in range(self.n):
        #             #         self.M[i][j] /= div
        #             # print(self.E[i],"aaaaaaaaaaaaaaaa")
        #             self.E[i] = int(self.E[i])
        #             # if not co_prime(pix, self.E[i]):
        #             #     self.E[i] /= gcd(pix, self.E[i])
        #             for j in range(self.n):
        #                 self.M[i][j] = 1
        #         else:
        #             div = gcd(pix, self.E[i], self.C[i])
        #             # self.E[i] /= div
        #             self.C[i] /= div
        #             pix /= div
        #             for j in range(self.n):
        #                 self.M[i][j] /= div
        #             div = gcd(int(pix), int(self.C[i]))
        #             for j in range(self.n):
        #                 self.M[i][j] /= div
        #             self.C[i] /= div
        # for i in range(self.h):
        #     divisior = gcd(*self.A[i], self.B[i])
        #     self.B[i] /= divisior
        #     for j in range(self.n):
        #         self.A[i][j] /= divisior
        # # for i in range(len(self.E)):
        # #     self.E[i] = int(self.E[i])
        # # print(self.E,"bbbbbbbbbbbbbbbbbbbbbb")

    def Max_list(self,x):
        i = 0
        max = x[i] #将列表中第一个值定义为最大值
        for i in range(len(x)):
            if max < x[i]:
                max = x[i] # for循环实现寻找列表中的最大值
        for m in range(len(x)):
            if x[m] == max:
                return m #  寻找并输出所有最大值的下标

    def formula_model1(self, n_set, p_set, *val):  # 得到一个公式模型   kd：代入变量求得变量，代入数值就是求得一个值
        # print("###############33",val)

        n_set = list(n_set)
        p_set = list(p_set)
        # print(n_set)
        if len(val) == 0:
            val = self.vi
        formu = []
        # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!1
        for k in range(self.k):
            clause = []
            val_s = [0,0,0,0,0,0,0,0]
            for h in range(self.h):
                # print(self.A,"@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@22")
                Coe = combine(self.A[h][j] * val[j] for j in range(self.n))
                # status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
                # print(Coe , "3####3333333333",status)
                # print(Coe, "asdffff1111111111111111111111111111111f", self.B[h])
                if (len(n_set) == 0) and (len(p_set) == 0):
                    status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
                    if status == (False, False, True):  # 选择大于小于等于
                        clause.append(Coe <= self.B[h])
                    elif status == (False, True, False):
                        clause.append(Coe >= self.B[h])
                    elif status == (True, False, False):
                        clause.append(Coe != self.B[h])
                    elif status == (False, True, True):
                        clause.append(Coe == self.B[h])
                    elif status == (True, False, True):
                        clause.append(Coe < self.B[h])
                    elif status == (True, True, False):
                        clause.append(Coe > self.B[h])
                    elif status == (True, True, True):
                        clause.append(False)

                else:

                    for i in range(len(n_set)):
                        s1 = Solver()
                        s1.set("timeout", 600000)
                        s1.add(Coe != self.B[h])
                        if (len(n_set[i]) == 1):
                            s1.add(val[0] == n_set[i][0])
                        elif (len(n_set[i]) == 2):
                            s1.add(val[0] == n_set[i][0])
                            s1.add(val[1] == n_set[i][1])
                        elif (len(n_set[i]) == 3):
                            s1.add(val[0] == n_set[i][0])
                            s1.add(val[1] == n_set[i][1])
                            s1.add(val[2] == n_set[i][2])
                        elif (len(n_set[i]) == 4):
                            s1.add(val[0] == n_set[i][0])
                            s1.add(val[1] == n_set[i][1])
                            s1.add(val[2] == n_set[i][2])
                            s1.add(val[3] == n_set[i][3])
                        if s1.check() == sat:
                            val_s[0] = val_s[0] + 1


                    for i in range(len(p_set)):
                        s1 = Solver()
                        s1.set("timeout", 600000)
                        s1.add(Coe != self.B[h])
                        if (len(p_set[i]) == 1):
                            s1.add(val[0] == p_set[i][0])
                        elif (len(p_set[i]) == 2):
                            s1.add(val[0] == p_set[i][0])
                            s1.add(val[1] == p_set[i][1])
                        elif (len(p_set[i]) == 3):
                            s1.add(val[0] == p_set[i][0])
                            s1.add(val[1] == p_set[i][1])
                            s1.add(val[2] == p_set[i][2])
                        elif (len(p_set[i]) == 4):
                            s1.add(val[0] == p_set[i][0])
                            s1.add(val[1] == p_set[i][1])
                            s1.add(val[2] == p_set[i][2])
                            s1.add(val[3] == p_set[i][3])
                        # s1.add(self.A[h][j] * n_set[i][0] for j in range(self.n))
                        # s1.add(self.A[h][j] * n_set[i] for j in range(self.n))
                        if s1.check() == unsat:
                            val_s[0] = val_s[0] + 1

                    # clause.append(Coe != self.B[h])
                    # self.He[k][h] = True
                    # self.Hge[k][h] = False
                    # self.Hle[k][h] = False


                    for i in range(len(n_set)):
                        s2 = Solver()
                        s2.set("timeout", 600000)
                        s2.add(Coe == self.B[h])
                        if (len(n_set[i]) == 1):
                            s2.add(val[0] == n_set[i][0])
                        elif (len(n_set[i]) == 2):
                            s2.add(val[0] == n_set[i][0])
                            s2.add(val[1] == n_set[i][1])
                        elif (len(n_set[i]) == 3):
                            s2.add(val[0] == n_set[i][0])
                            s2.add(val[1] == n_set[i][1])
                            s2.add(val[2] == n_set[i][2])
                        elif (len(n_set[i]) == 4):
                            s2.add(val[0] == n_set[i][0])
                            s2.add(val[1] == n_set[i][1])
                            s2.add(val[2] == n_set[i][2])
                            s2.add(val[3] == n_set[i][3])
                        if s2.check() == sat:
                            val_s[1] = val_s[1] + 1

                    for i in range(len(p_set)):
                        s2 = Solver()
                        s2.set("timeout", 600000)
                        s2.add(Coe == self.B[h])
                        if (len(p_set[i]) == 1):
                            s2.add(val[0] == p_set[i][0])
                        elif (len(p_set[i]) == 2):
                            s2.add(val[0] == p_set[i][0])
                            s2.add(val[1] == p_set[i][1])
                        elif (len(p_set[i]) == 3):
                            s2.add(val[0] == p_set[i][0])
                            s2.add(val[1] == p_set[i][1])
                            s2.add(val[2] == p_set[i][2])
                        elif (len(p_set[i]) == 4):
                            s2.add(val[0] == p_set[i][0])
                            s2.add(val[1] == p_set[i][1])
                            s2.add(val[2] == p_set[i][2])
                            s2.add(val[3] == p_set[i][3])
                        if s2.check() == unsat:
                            val_s[1] = val_s[1] + 1

                    # clause.append(Coe == self.B[h])

                    # self.He[k][h] = False
                    # self.Hge[k][h] = True
                    # self.Hle[k][h] = True



                    for i in range(len(n_set)):
                        s3 = Solver()
                        s3.set("timeout", 600000)
                        s3.add(Coe > self.B[h])
                        if (len(n_set[i]) == 1):
                            s3.add(val[0] == n_set[i][0])
                        elif (len(n_set[i]) == 2):
                            s3.add(val[0] == n_set[i][0])
                            s3.add(val[1] == n_set[i][1])
                        elif (len(n_set[i]) == 3):
                            s3.add(val[0] == n_set[i][0])
                            s3.add(val[1] == n_set[i][1])
                            s3.add(val[2] == n_set[i][2])
                        elif (len(n_set[i]) == 4):
                            s3.add(val[0] == n_set[i][0])
                            s3.add(val[1] == n_set[i][1])
                            s3.add(val[2] == n_set[i][2])
                            s3.add(val[3] == n_set[i][3])
                        if s3.check() ==  sat:
                            val_s[2] = val_s[2] + 1

                    for i in range(len(p_set)):
                        s3 = Solver()
                        s3.set("timeout", 600000)
                        s3.add(Coe > self.B[h])
                        if (len(p_set[i]) == 1):
                            s3.add(val[0] == p_set[i][0])
                        elif (len(p_set[i]) == 2):
                            s3.add(val[0] == p_set[i][0])
                            s3.add(val[1] == p_set[i][1])
                        elif (len(p_set[i]) == 3):
                            s3.add(val[0] == p_set[i][0])
                            s3.add(val[1] == p_set[i][1])
                            s3.add(val[2] == p_set[i][2])
                        elif (len(p_set[i]) == 4):
                            s3.add(val[0] == p_set[i][0])
                            s3.add(val[1] == p_set[i][1])
                            s3.add(val[2] == p_set[i][2])
                            s3.add(val[3] == p_set[i][3])
                        if s3.check() == unsat:
                            val_s[2] = val_s[2] + 1

                    # clause.append(Coe > self.B[h])
                    #
                    #             self.He[k][h] = True
                    #             self.Hge[k][h] = True
                    #             self.Hle[k][h] = False


                    for i in range(len(n_set)):
                        s4 = Solver()
                        s4.set("timeout", 600000)
                        s4.add(Coe < self.B[h])
                        if (len(n_set[i]) == 1):
                            s4.add(val[0] == n_set[i][0])
                        elif (len(n_set[i]) == 2):
                            s4.add(val[0] == n_set[i][0])
                            s4.add(val[1] == n_set[i][1])
                        elif (len(n_set[i]) == 3):
                            s4.add(val[0] == n_set[i][0])
                            s4.add(val[1] == n_set[i][1])
                            s4.add(val[2] == n_set[i][2])
                        elif (len(n_set[i]) == 4):
                            s4.add(val[0] == n_set[i][0])
                            s4.add(val[1] == n_set[i][1])
                            s4.add(val[2] == n_set[i][2])
                            s4.add(val[3] == n_set[i][3])
                        if s4.check() == sat:
                            val_s[3] = val_s[3] + 1

                    for i in range(len(p_set)):
                        s4 = Solver()
                        s4.set("timeout", 600000)
                        s4.add(Coe < self.B[h])
                        if (len(p_set[i]) == 1):
                            s4.add(val[0] == p_set[i][0])
                        elif (len(p_set[i]) == 2):
                            s4.add(val[0] == p_set[i][0])
                            s4.add(val[1] == p_set[i][1])
                        elif (len(p_set[i]) == 3):
                            s4.add(val[0] == p_set[i][0])
                            s4.add(val[1] == p_set[i][1])
                            s4.add(val[2] == p_set[i][2])
                        elif (len(p_set[i]) == 4):
                            s4.add(val[0] == p_set[i][0])
                            s4.add(val[1] == p_set[i][1])
                            s4.add(val[2] == p_set[i][2])
                            s4.add(val[3] == p_set[i][3])
                        if s4.check() == unsat:
                            val_s[3] = val_s[3] + 1
                            # if flag4 == 0:
                            #     clause.append(Coe < self.B[h])
                            #
                            #     self.He[k][h] = True
                            #     self.Hge[k][h] = False
                            #     self.Hle[k][h] = True


                    for i in range(len(n_set)):
                        s5 = Solver()
                        s5.set("timeout", 600000)
                        s5.add(Coe <= self.B[h])
                        if (len(n_set[i]) == 1):
                            s5.add(val[0] == n_set[i][0])
                        elif (len(n_set[i]) == 2):
                            s5.add(val[0] == n_set[i][0])
                            s5.add(val[1] == n_set[i][1])
                        elif (len(n_set[i]) == 3):
                            s5.add(val[0] == n_set[i][0])
                            s5.add(val[1] == n_set[i][1])
                            s5.add(val[2] == n_set[i][2])
                        elif (len(n_set[i]) == 4):
                            s5.add(val[0] == n_set[i][0])
                            s5.add(val[1] == n_set[i][1])
                            s5.add(val[2] == n_set[i][2])
                            s5.add(val[3] == n_set[i][3])
                        if s5.check() ==  sat:
                            val_s[4] = val_s[4] + 1

                    for i in range(len(p_set)):
                        s5 = Solver()
                        s5.set("timeout", 600000)
                        s5.add(Coe <= self.B[h])
                        if (len(p_set[i]) == 1):
                            s5.add(val[0] == p_set[i][0])
                        elif (len(p_set[i]) == 2):
                            s5.add(val[0] == p_set[i][0])
                            s5.add(val[1] == p_set[i][1])
                        elif (len(p_set[i]) == 3):
                            s5.add(val[0] == p_set[i][0])
                            s5.add(val[1] == p_set[i][1])
                            s5.add(val[2] == p_set[i][2])
                        elif (len(p_set[i]) == 4):
                            s5.add(val[0] == p_set[i][0])
                            s5.add(val[1] == p_set[i][1])
                            s5.add(val[2] == p_set[i][2])
                            s5.add(val[3] == p_set[i][3])
                        if s5.check() == unsat:
                            val_s[4] = val_s[4] + 1

                                    # clause.append(Coe <= self.B[h])
                                    #
                                    # self.He[k][h] = False
                                    # self.Hge[k][h] = False
                                    # self.Hle[k][h] = True



                    for i in range(len(n_set)):
                        s6 = Solver()
                        s6.set("timeout", 600000)
                        s6.add(Coe >= self.B[h])
                        if (len(n_set[i]) == 1):
                            s6.add(val[0] == n_set[i][0])
                        elif (len(n_set[i]) == 2):
                            s6.add(val[0] == n_set[i][0])
                            s6.add(val[1] == n_set[i][1])
                        elif (len(n_set[i]) == 3):
                            s6.add(val[0] == n_set[i][0])
                            s6.add(val[1] == n_set[i][1])
                            s6.add(val[2] == n_set[i][2])
                        elif (len(n_set[i]) == 4):
                            s6.add(val[0] == n_set[i][0])
                            s6.add(val[1] == n_set[i][1])
                            s6.add(val[2] == n_set[i][2])
                            s6.add(val[3] == n_set[i][3])
                        # print(s6.check(),"setsetsetsetsetse")
                        if s6.check() == sat:
                            val_s[5] = val_s[5] + 1

                    for i in range(len(p_set)):
                        s6 = Solver()
                        s6.set("timeout", 600000)
                        s6.add(Coe >= self.B[h])
                        if (len(p_set[i]) == 1):
                            s6.add(val[0] == p_set[i][0])
                        elif (len(p_set[i]) == 2):
                            s6.add(val[0] == p_set[i][0])
                            s6.add(val[1] == p_set[i][1])
                        elif (len(p_set[i]) == 3):
                            s6.add(val[0] == p_set[i][0])
                            s6.add(val[1] == p_set[i][1])
                            s6.add(val[2] == p_set[i][2])
                        elif (len(p_set[i]) == 4):
                            s6.add(val[0] == p_set[i][0])
                            s6.add(val[1] == p_set[i][1])
                            s6.add(val[2] == p_set[i][2])
                            s6.add(val[3] == p_set[i][3])
                        # print(s6.check(),"testestestestests")
                        if s6.check() == unsat:
                            val_s[5] = val_s[5] + 1


                    max_i = self.Max_list(val_s)
                    if(val_s[max_i] == (len(n_set) + len(p_set))):
                        if(max_i == 0):
                            clause.append(Coe != self.B[h])
                            self.He[k][h] = True
                            self.Hge[k][h] = False
                            self.Hle[k][h] = False
                        elif(max_i == 1):
                            clause.append(Coe == self.B[h])
                            self.He[k][h] = False
                            self.Hge[k][h] = True
                            self.Hle[k][h] = True
                        elif(max_i==2):
                            clause.append(Coe > self.B[h])
                            self.He[k][h] = True
                            self.Hge[k][h] = True
                            self.Hle[k][h] = False
                        elif(max_i==3):
                            clause.append(Coe < self.B[h])
                            self.He[k][h] = True
                            self.Hge[k][h] = False
                            self.Hle[k][h] = True
                        elif(max_i == 4):
                            clause.append(Coe <= self.B[h])
                            self.He[k][h] = False
                            self.Hge[k][h] = False
                            self.Hle[k][h] = True
                        else:
                            clause.append(Coe >= self.B[h])
                            self.He[k][h] = False
                            self.Hge[k][h] = True
                            self.Hle[k][h] = False
                    # else:
                    #     clause.append(False)
                    #     self.He[k][h] = True
                    #     self.Hge[k][h] = True
                    #     self.Hle[k][h] = True








        print(clause,"oooooooooooooooooooooooooooooooooooooooo" )

        for m in range(self.m):
            val_sm = [0,0]
            if (len(n_set) == 0) and (len(p_set) == 0):
                status = (self.T[k][m], self.Nt[k][m])
                if status == (True, False):  # 选择取模
                    clause.append(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                elif status == (False, True):

                    clause.append(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
                elif status == (True, True):
                    clause.append(False)
            else:


                for i in range(len(n_set)):
                    s7 = Solver()
                    s7.set("timeout", 600000)
                    s7.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])

                    if (len(n_set[i]) == 1):

                        s7.add(val[0] == n_set[i][0])

                    elif (len(n_set[i]) == 2):
                        s7.add(val[0] == n_set[i][0])
                        s7.add(val[1] == n_set[i][1])
                    elif (len(n_set[i]) == 3):
                        s7.add(val[0] == n_set[i][0])
                        s7.add(val[1] == n_set[i][1])
                        s7.add(val[2] == n_set[i][2])
                    elif (len(n_set[i]) == 4):
                        s7.add(val[0] == n_set[i][0])
                        s7.add(val[1] == n_set[i][1])
                        s7.add(val[2] == n_set[i][2])
                        s7.add(val[3] == n_set[i][3])
                    if s7.check() == sat:
                        val_sm[0] = val_sm[0] +1


                for i in range(len(p_set)):
                    s7 = Solver()
                    s7.set("timeout", 600000)
                    # print("self.E[i]",self.E[m],self.n)
                    s7.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])

                    if (len(p_set[i]) == 1):
                        # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
                        # print(val[0])
                        # print(n_set[i][0])

                        s7.add(val[0] == p_set[i][0])
                        # print(s7.check())
                    elif (len(p_set[i]) == 2):
                        s7.add(val[0] == p_set[i][0])
                        s7.add(val[1] == p_set[i][1])
                    elif (len(p_set[i]) == 3):
                        s7.add(val[0] == p_set[i][0])
                        s7.add(val[1] == p_set[i][1])
                        s7.add(val[2] == p_set[i][2])
                    elif (len(p_set[i]) == 4):
                        s7.add(val[0] == p_set[i][0])
                        s7.add(val[1] == p_set[i][1])
                        s7.add(val[2] == p_set[i][2])
                        s7.add(val[3] == p_set[i][3])
                    if s7.check() == unsat:
                        val_sm[0] = val_sm[0] + 1
                # if flag7 == 0:
                #     clause.append(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
                #     for j in range(self.n):
                #         self.M[m][j] = 1
                #
                #     self.T[k][m] = False
                #     self.Nt[k][m] = True
                #     break

                for i in range(len(n_set)):
                    s8 = Solver()
                    s8.set("timeout", 600000)

                    s8.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                    if (len(n_set[i]) == 1):
                        # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                        # print(val[0])
                        # print(n_set[i][0])

                        s8.add(val[0] == n_set[i][0])
                        # print(s8.check())
                    elif (len(n_set[i]) == 2):
                        s8.add(val[0] == n_set[i][0])
                        s8.add(val[1] == n_set[i][1])
                    elif (len(n_set[i]) == 3):
                        s8.add(val[0] == n_set[i][0])
                        s8.add(val[1] == n_set[i][1])
                        s8.add(val[2] == n_set[i][2])
                    elif (len(n_set[i]) == 4):
                        s8.add(val[0] == n_set[i][0])
                        s8.add(val[1] == n_set[i][1])
                        s8.add(val[2] == n_set[i][2])
                        s8.add(val[3] == n_set[i][3])
                    if s8.check() ==  sat:
                        val_sm[1] = val_sm[1] + 1

                for i in range(len(p_set)):
                    s8 = Solver()
                    s8.set("timeout", 600000)

                    s8.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                    if (len(p_set[i]) == 1):
                        # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                        # print(val[0])
                        # print(n_set[i][0])

                        s8.add(val[0] == p_set[i][0])
                        # print(s8.check())
                    elif (len(p_set[i]) == 2):
                        s8.add(val[0] == p_set[i][0])
                        s8.add(val[1] == p_set[i][1])
                    elif (len(p_set[i]) == 3):
                        s8.add(val[0] == p_set[i][0])
                        s8.add(val[1] == p_set[i][1])
                        s8.add(val[2] == p_set[i][2])
                    elif (len(p_set[i]) == 4):
                        s8.add(val[0] == p_set[i][0])
                        s8.add(val[1] == p_set[i][1])
                        s8.add(val[2] == p_set[i][2])
                        s8.add(val[3] == p_set[i][3])
                    if s8.check() == unsat:
                        val_sm[1] = val_sm[1] + 1
                max_i = self.Max_list(val_sm)
                if(max_i == 0):
                    clause.append(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
                    for j in range(self.n):
                        self.M[m][j] = 1
                    self.T[k][m] = False
                    self.Nt[k][m] = True
                else:
                    clause.append(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                    for j in range(self.n):
                        self.M[m][j] = 1
                    self.T[k][m] = True
                    self.Nt[k][m] = False


                    # if flag8 == 0:
                    #     clause.append(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
                    #     for j in range(self.n):
                    #         self.M[m][j] = 1
                    #     self.T[k][m] = True
                    #     self.Nt[k][m] = False
                    #     break
                    # else:
                    #     clause.append(False)
                    #     self.T[k][m] = True
                    #     self.Nt[k][m] = True


        print(clause, "Aaaaaaa/aaaaaaaaaaaaaaaaaaaaaaaaaaaaa")

        formu.append(And(*clause))

        print(formu)
        print("simplify(Or(*formu))=\n",simplify(Or(*formu)))
        return simplify(Or(*formu))
    ####################################################################3
    # def formula_model1(self,n_set,p_set, *val):  # 得到一个公式模型   kd：代入变量求得变量，代入数值就是求得一个值
    #     # print("###############33",val)
    #     n_set = list(n_set)
    #     p_set = list(p_set)
    #     # print(n_set)
    #     if len(val) == 0:
    #         val = self.vi
    #     formu = []
    #     #!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!1
    #     for k in range(self.k):
    #         clause = []
    #
    #         for h in range(self.h):
    #             # print(self.A,"@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@22")
    #             Coe = combine(self.A[h][j] * val[j] for j in range(self.n))
    #             # status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
    #             # print(Coe , "3####3333333333",status)
    #             # print(Coe, "asdffff1111111111111111111111111111111f", self.B[h])
    #             if(len(n_set) ==0) and (len(p_set)==0):
    #                 status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
    #                 if status == (False, False, True):  # 选择大于小于等于
    #                     clause.append(Coe <= self.B[h])
    #                 elif status == (False, True, False):
    #                     clause.append(Coe >= self.B[h])
    #                 elif status == (True, False, False):
    #                     clause.append(Coe != self.B[h])
    #                 elif status == (False, True, True):
    #                     clause.append(Coe == self.B[h])
    #                 elif status == (True, False, True):
    #                     clause.append(Coe < self.B[h])
    #                 elif status == (True, True, False):
    #                     clause.append(Coe > self.B[h])
    #                 elif status == (True, True, True):
    #                     clause.append(False)
    #
    #             else:
    #                 # print(Coe , "asdfffffffffffffffffffffffffff",self.B[h])
    #                 flag1 = 0
    #                 for i in range(len(n_set)):
    #                     s1 = Solver()
    #                     s1.set("timeout", 600000)
    #                     s1.add(Coe != self.B[h])
    #                     if(len(n_set[i]) == 1):
    #                         s1.add(val[0] == n_set[i][0])
    #                     elif(len(n_set[i]) == 2):
    #                         s1.add(val[0] == n_set[i][0])
    #                         s1.add(val[1] == n_set[i][1])
    #                     elif(len(n_set[i]) == 3):
    #                         s1.add(val[0] == n_set[i][0])
    #                         s1.add(val[1] == n_set[i][1])
    #                         s1.add(val[2] == n_set[i][2])
    #                     elif(len(n_set[i])==4):
    #                         s1.add(val[0] == n_set[i][0])
    #                         s1.add(val[1] == n_set[i][1])
    #                         s1.add(val[2] == n_set[i][2])
    #                         s1.add(val[3] == n_set[i][3])
    #                     if s1.check() == unsat:
    #                         flag1 = 1
    #                 if flag1 == 0:
    #                     for i in range(len(p_set)):
    #                         s1 = Solver()
    #                         s1.set("timeout", 600000)
    #                         s1.add(Coe != self.B[h])
    #                         if (len(p_set[i]) == 1):
    #                             s1.add(val[0] == p_set[i][0])
    #                         elif (len(p_set[i]) == 2):
    #                             s1.add(val[0] == p_set[i][0])
    #                             s1.add(val[1] == p_set[i][1])
    #                         elif (len(p_set[i]) == 3):
    #                             s1.add(val[0] == p_set[i][0])
    #                             s1.add(val[1] == p_set[i][1])
    #                             s1.add(val[2] == p_set[i][2])
    #                         elif (len(p_set[i]) == 4):
    #                             s1.add(val[0] == p_set[i][0])
    #                             s1.add(val[1] == p_set[i][1])
    #                             s1.add(val[2] == p_set[i][2])
    #                             s1.add(val[3] == p_set[i][3])
    #                         # s1.add(self.A[h][j] * n_set[i][0] for j in range(self.n))
    #                         # s1.add(self.A[h][j] * n_set[i] for j in range(self.n))
    #                         if s1.check() == sat:
    #                             flag1 = 1
    #                 if flag1 == 0:
    #                     clause.append(Coe != self.B[h])
    #                     self.He[k][h] = True
    #                     self.Hge[k][h] = False
    #                     self.Hle[k][h] = False
    #                     break
    #                 else :
    #                     flag2 = 0
    #                     for i in range(len(n_set)):
    #                         s2 = Solver()
    #                         s2.set("timeout", 600000)
    #                         s2.add(Coe == self.B[h])
    #                         if (len(n_set[i]) == 1):
    #                             s2.add(val[0] == n_set[i][0])
    #                         elif (len(n_set[i]) == 2):
    #                             s2.add(val[0] == n_set[i][0])
    #                             s2.add(val[1] == n_set[i][1])
    #                         elif (len(n_set[i]) == 3):
    #                             s2.add(val[0] == n_set[i][0])
    #                             s2.add(val[1] == n_set[i][1])
    #                             s2.add(val[2] == n_set[i][2])
    #                         elif (len(n_set[i]) == 4):
    #                             s2.add(val[0] == n_set[i][0])
    #                             s2.add(val[1] == n_set[i][1])
    #                             s2.add(val[2] == n_set[i][2])
    #                             s2.add(val[3] == n_set[i][3])
    #                         if s2.check() == unsat:
    #                             flag2 = 1
    #                     if flag2 == 0:
    #                         for i in range(len(p_set)):
    #                             s2 = Solver()
    #                             s2.set("timeout", 600000)
    #                             s2.add(Coe == self.B[h])
    #                             if (len(p_set[i]) == 1):
    #                                 s2.add(val[0] == p_set[i][0])
    #                             elif (len(p_set[i]) == 2):
    #                                 s2.add(val[0] == p_set[i][0])
    #                                 s2.add(val[1] == p_set[i][1])
    #                             elif (len(p_set[i]) == 3):
    #                                 s2.add(val[0] == p_set[i][0])
    #                                 s2.add(val[1] == p_set[i][1])
    #                                 s2.add(val[2] == p_set[i][2])
    #                             elif (len(p_set[i]) == 4):
    #                                 s2.add(val[0] == p_set[i][0])
    #                                 s2.add(val[1] == p_set[i][1])
    #                                 s2.add(val[2] == p_set[i][2])
    #                                 s2.add(val[3] == p_set[i][3])
    #                             if s2.check() == sat:
    #                                 flag2 = 1
    #                     if flag2 == 0:
    #                         clause.append(Coe == self.B[h])
    #
    #                         self.He[k][h] = False
    #                         self.Hge[k][h] = True
    #                         self.Hle[k][h] = True
    #                         break
    #                     else:
    #                         flag3 = 0
    #                         for i in range(len(n_set)):
    #                             s3 = Solver()
    #                             s3.set("timeout", 600000)
    #                             s3.add(Coe > self.B[h])
    #                             if (len(n_set[i]) == 1):
    #                                 s3.add(val[0] == n_set[i][0])
    #                             elif (len(n_set[i]) == 2):
    #                                 s3.add(val[0] == n_set[i][0])
    #                                 s3.add(val[1] == n_set[i][1])
    #                             elif (len(n_set[i]) == 3):
    #                                 s3.add(val[0] == n_set[i][0])
    #                                 s3.add(val[1] == n_set[i][1])
    #                                 s3.add(val[2] == n_set[i][2])
    #                             elif (len(n_set[i]) == 4):
    #                                 s3.add(val[0] == n_set[i][0])
    #                                 s3.add(val[1] == n_set[i][1])
    #                                 s3.add(val[2] == n_set[i][2])
    #                                 s3.add(val[3] == n_set[i][3])
    #                             if s3.check() == unsat:
    #                                 flag3 = 1
    #                         if flag3 == 0:
    #                             for i in range(len(p_set)):
    #                                 s3 = Solver()
    #                                 s3.set("timeout", 600000)
    #                                 s3.add(Coe > self.B[h])
    #                                 if (len(p_set[i]) == 1):
    #                                     s3.add(val[0] == p_set[i][0])
    #                                 elif (len(p_set[i]) == 2):
    #                                     s3.add(val[0] == p_set[i][0])
    #                                     s3.add(val[1] == p_set[i][1])
    #                                 elif (len(p_set[i]) == 3):
    #                                     s3.add(val[0] == p_set[i][0])
    #                                     s3.add(val[1] == p_set[i][1])
    #                                     s3.add(val[2] == p_set[i][2])
    #                                 elif (len(p_set[i]) == 4):
    #                                     s3.add(val[0] == p_set[i][0])
    #                                     s3.add(val[1] == p_set[i][1])
    #                                     s3.add(val[2] == p_set[i][2])
    #                                     s3.add(val[3] == p_set[i][3])
    #                                 if s3.check() == sat:
    #                                     flag3 = 1
    #                         if flag3 == 0:
    #                             clause.append(Coe > self.B[h])
    #
    #                             self.He[k][h] = True
    #                             self.Hge[k][h] = True
    #                             self.Hle[k][h] = False
    #                             break
    #                         else:
    #                             flag4 = 0
    #                             for i in range(len(n_set)):
    #                                 s4 = Solver()
    #                                 s4.set("timeout", 600000)
    #                                 s4.add(Coe < self.B[h])
    #                                 if (len(n_set[i]) == 1):
    #                                     s4.add(val[0] == n_set[i][0])
    #                                 elif (len(n_set[i]) == 2):
    #                                     s4.add(val[0] == n_set[i][0])
    #                                     s4.add(val[1] == n_set[i][1])
    #                                 elif (len(n_set[i]) == 3):
    #                                     s4.add(val[0] == n_set[i][0])
    #                                     s4.add(val[1] == n_set[i][1])
    #                                     s4.add(val[2] == n_set[i][2])
    #                                 elif (len(n_set[i]) == 4):
    #                                     s4.add(val[0] == n_set[i][0])
    #                                     s4.add(val[1] == n_set[i][1])
    #                                     s4.add(val[2] == n_set[i][2])
    #                                     s4.add(val[3] == n_set[i][3])
    #                                 if s4.check() == unsat:
    #                                     flag4 = 1
    #                             if flag4 == 0 :
    #                                 for i in range(len(p_set)):
    #                                     s4 = Solver()
    #                                     s4.set("timeout", 600000)
    #                                     s4.add(Coe < self.B[h])
    #                                     if (len(p_set[i]) == 1):
    #                                         s4.add(val[0] == p_set[i][0])
    #                                     elif (len(p_set[i]) == 2):
    #                                         s4.add(val[0] == p_set[i][0])
    #                                         s4.add(val[1] == p_set[i][1])
    #                                     elif (len(p_set[i]) == 3):
    #                                         s4.add(val[0] == p_set[i][0])
    #                                         s4.add(val[1] == p_set[i][1])
    #                                         s4.add(val[2] == p_set[i][2])
    #                                     elif (len(p_set[i]) == 4):
    #                                         s4.add(val[0] == p_set[i][0])
    #                                         s4.add(val[1] == p_set[i][1])
    #                                         s4.add(val[2] == p_set[i][2])
    #                                         s4.add(val[3] == p_set[i][3])
    #                                     if s4.check() == sat:
    #                                         flag4 = 1
    #                             if flag4 == 0:
    #                                 clause.append(Coe < self.B[h])
    #
    #                                 self.He[k][h] = True
    #                                 self.Hge[k][h] = False
    #                                 self.Hle[k][h] = True
    #                                 break
    #                             else:
    #                                 flag5 = 0
    #                                 for i in range(len(n_set)):
    #                                     s5 = Solver()
    #                                     s5.set("timeout", 600000)
    #                                     s5.add(Coe <= self.B[h])
    #                                     if (len(n_set[i]) == 1):
    #                                         s5.add(val[0] == n_set[i][0])
    #                                     elif (len(n_set[i]) == 2):
    #                                         s5.add(val[0] == n_set[i][0])
    #                                         s5.add(val[1] == n_set[i][1])
    #                                     elif (len(n_set[i]) == 3):
    #                                         s5.add(val[0] == n_set[i][0])
    #                                         s5.add(val[1] == n_set[i][1])
    #                                         s5.add(val[2] == n_set[i][2])
    #                                     elif (len(n_set[i]) == 4):
    #                                         s5.add(val[0] == n_set[i][0])
    #                                         s5.add(val[1] == n_set[i][1])
    #                                         s5.add(val[2] == n_set[i][2])
    #                                         s5.add(val[3] == n_set[i][3])
    #                                     if s5.check() == unsat:
    #                                         flag5 = 1
    #                                 if flag5 == 0:
    #                                     for i in range(len(p_set)):
    #                                         s5 = Solver()
    #                                         s5.set("timeout", 600000)
    #                                         s5.add(Coe <= self.B[h])
    #                                         if (len(p_set[i]) == 1):
    #                                             s5.add(val[0] == p_set[i][0])
    #                                         elif (len(p_set[i]) == 2):
    #                                             s5.add(val[0] == p_set[i][0])
    #                                             s5.add(val[1] == p_set[i][1])
    #                                         elif (len(p_set[i]) == 3):
    #                                             s5.add(val[0] == p_set[i][0])
    #                                             s5.add(val[1] == p_set[i][1])
    #                                             s5.add(val[2] == p_set[i][2])
    #                                         elif (len(p_set[i]) == 4):
    #                                             s5.add(val[0] == p_set[i][0])
    #                                             s5.add(val[1] == p_set[i][1])
    #                                             s5.add(val[2] == p_set[i][2])
    #                                             s5.add(val[3] == p_set[i][3])
    #                                         if s5.check() == sat:
    #                                             flag5 = 1
    #                                 if flag5 == 0:
    #                                     clause.append(Coe <= self.B[h])
    #
    #                                     self.He[k][h] = False
    #                                     self.Hge[k][h] = False
    #                                     self.Hle[k][h] = True
    #                                     break
    #                                 else:
    #                                     flag6 = 0
    #                                     for i in range(len(n_set)):
    #                                         s6 = Solver()
    #                                         s6.set("timeout", 600000)
    #                                         s6.add(Coe >= self.B[h])
    #                                         if (len(n_set[i]) == 1):
    #                                             s6.add(val[0] == n_set[i][0])
    #                                         elif (len(n_set[i]) == 2):
    #                                             s6.add(val[0] == n_set[i][0])
    #                                             s6.add(val[1] == n_set[i][1])
    #                                         elif (len(n_set[i]) == 3):
    #                                             s6.add(val[0] == n_set[i][0])
    #                                             s6.add(val[1] == n_set[i][1])
    #                                             s6.add(val[2] == n_set[i][2])
    #                                         elif (len(n_set[i]) == 4):
    #                                             s6.add(val[0] == n_set[i][0])
    #                                             s6.add(val[1] == n_set[i][1])
    #                                             s6.add(val[2] == n_set[i][2])
    #                                             s6.add(val[3] == n_set[i][3])
    #                                         # print(s6.check(),"setsetsetsetsetse")
    #                                         if s6.check() == unsat:
    #                                             flag6 = 1
    #                                     if flag6 == 0:
    #                                         for i in range(len(p_set)):
    #                                             s6 = Solver()
    #                                             s6.set("timeout", 600000)
    #                                             s6.add(Coe >= self.B[h])
    #                                             if (len(p_set[i]) == 1):
    #                                                 s6.add(val[0] == p_set[i][0])
    #                                             elif (len(p_set[i]) == 2):
    #                                                 s6.add(val[0] == p_set[i][0])
    #                                                 s6.add(val[1] == p_set[i][1])
    #                                             elif (len(p_set[i]) == 3):
    #                                                 s6.add(val[0] == p_set[i][0])
    #                                                 s6.add(val[1] == p_set[i][1])
    #                                                 s6.add(val[2] == p_set[i][2])
    #                                             elif (len(p_set[i]) == 4):
    #                                                 s6.add(val[0] == p_set[i][0])
    #                                                 s6.add(val[1] == p_set[i][1])
    #                                                 s6.add(val[2] == p_set[i][2])
    #                                                 s6.add(val[3] == p_set[i][3])
    #                                             # print(s6.check(),"testestestestests")
    #                                             if s6.check() == sat:
    #                                                 flag6 = 1
    #                                     if flag6 == 0:
    #                                         clause.append(Coe >= self.B[h])
    #                                         self.He[k][h] = False
    #                                         self.Hge[k][h] = True
    #                                         self.Hle[k][h] = False
    #                                         break
    #                                     else:
    #                                         clause.append(False)
    #                                         self.He[k][h] = True
    #                                         self.Hge[k][h] = True
    #                                         self.Hle[k][h] = True
    #                                         # fg = 1
    #                                         # status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
    #                                         # if status == (False, False, True):  # 选择大于小于等于
    #                                         #     clause.append(Coe <= self.B[h])
    #                                         # elif status == (False, True, False):
    #                                         #     clause.append(Coe >= self.B[h])
    #                                         # elif status == (True, False, False):
    #                                         #     clause.append(Coe != self.B[h])
    #                                         # elif status == (False, True, True):
    #                                         #     clause.append(Coe == self.B[h])
    #                                         # elif status == (True, False, True):
    #                                         #     clause.append(Coe < self.B[h])
    #                                         # elif status == (True, True, False):
    #                                         #     clause.append(Coe > self.B[h])
    #                                         # elif status == (True, True, True):
    #                                         #     clause.append(False)
    #                                         break
    #     # print(clause,"oooooooooooooooooooooooooooooooooooooooo" )
    #
    #     for m in range(self.m):
    #         # print("self.m",self.m)
    #         # print(self.T[k][m], self.Nt[k][m])
    #         # print(",self.n  self.E[i]3333333333333333333333333333333333333333333",self.n,self.E[m],self.C[m])
    #         if(len(n_set) ==0) and (len(p_set)==0):
    #             status = (self.T[k][m], self.Nt[k][m])
    #             if status == (True, False):  # 选择取模
    #                 clause.append(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #             elif status == (False, True):
    #                 # print(self.M, val, self.E[m], self.C[m])
    #                 # print(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #                 clause.append(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #             elif status == (True, True):
    #                 clause.append(False)
    #         else:
    #
    #             flag7 = 0
    #             # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m],"222222222222222222222222")
    #             for i in range(len(n_set)):
    #                 s7 = Solver()
    #                 s7.set("timeout", 600000)
    #
    #                 # print("self.E[i]",self.E[m],self.n)
    #                 s7.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #
    #                 if(len(n_set[i]) == 1):
    #                     # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #                     # print(val[0])
    #                     # print(n_set[i][0])
    #
    #                     s7.add(val[0] == n_set[i][0])
    #                     # print(s7.check())
    #                 elif(len(n_set[i]) == 2):
    #                     s7.add(val[0] == n_set[i][0])
    #                     s7.add(val[1] == n_set[i][1])
    #                 elif(len(n_set[i]) == 3):
    #                     s7.add(val[0] == n_set[i][0])
    #                     s7.add(val[1] == n_set[i][1])
    #                     s7.add(val[2] == n_set[i][2])
    #                 elif(len(n_set[i])==4):
    #                     s7.add(val[0] == n_set[i][0])
    #                     s7.add(val[1] == n_set[i][1])
    #                     s7.add(val[2] == n_set[i][2])
    #                     s7.add(val[3] == n_set[i][3])
    #                 if s7.check() == unsat:
    #                     flag7 = 1
    #             if flag7 == 0:
    #                 for i in range(len(p_set)):
    #                     s7 = Solver()
    #                     s7.set("timeout", 600000)
    #                     # print("self.E[i]",self.E[m],self.n)
    #                     s7.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #
    #                     if (len(p_set[i]) == 1):
    #                         # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #                         # print(val[0])
    #                         # print(n_set[i][0])
    #
    #                         s7.add(val[0] == p_set[i][0])
    #                         # print(s7.check())
    #                     elif (len(p_set[i]) == 2):
    #                         s7.add(val[0] == p_set[i][0])
    #                         s7.add(val[1] == p_set[i][1])
    #                     elif (len(p_set[i]) == 3):
    #                         s7.add(val[0] == p_set[i][0])
    #                         s7.add(val[1] == p_set[i][1])
    #                         s7.add(val[2] == p_set[i][2])
    #                     elif (len(p_set[i]) == 4):
    #                         s7.add(val[0] == p_set[i][0])
    #                         s7.add(val[1] == p_set[i][1])
    #                         s7.add(val[2] == p_set[i][2])
    #                         s7.add(val[3] == p_set[i][3])
    #                     if s7.check() == sat:
    #                         flag7 = 1
    #             if flag7 == 0:
    #                 clause.append(combine(1 * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #                 for j in range(self.n):
    #                     self.M[m][j] =1
    #
    #                 self.T[k][m] = False
    #                 self.Nt[k][m] = True
    #                 break
    #             else:
    #                 flag8 = 0
    #                 # print("len(n_set)",len(n_set))
    #                 for i in range(len(n_set)):
    #                     s8 = Solver()
    #                     s8.set("timeout", 600000)
    #
    #                     s8.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #                     if (len(n_set[i]) == 1):
    #                         # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #                         # print(val[0])
    #                         # print(n_set[i][0])
    #
    #                         s8.add(val[0] == n_set[i][0])
    #                         # print(s8.check())
    #                     elif (len(n_set[i]) == 2):
    #                         s8.add(val[0] == n_set[i][0])
    #                         s8.add(val[1] == n_set[i][1])
    #                     elif (len(n_set[i]) == 3):
    #                         s8.add(val[0] == n_set[i][0])
    #                         s8.add(val[1] == n_set[i][1])
    #                         s8.add(val[2] == n_set[i][2])
    #                     elif (len(n_set[i]) == 4):
    #                         s8.add(val[0] == n_set[i][0])
    #                         s8.add(val[1] == n_set[i][1])
    #                         s8.add(val[2] == n_set[i][2])
    #                         s8.add(val[3] == n_set[i][3])
    #                     if s8.check() == unsat:
    #                         flag8 = 1
    #                 if flag8 == 0:
    #                     for i in range(len(p_set)):
    #                         s8 = Solver()
    #                         s8.set("timeout", 600000)
    #
    #                         s8.add(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #                         if (len(p_set[i]) == 1):
    #                             # print(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #                             # print(val[0])
    #                             # print(n_set[i][0])
    #
    #                             s8.add(val[0] == p_set[i][0])
    #                             # print(s8.check())
    #                         elif (len(p_set[i]) == 2):
    #                             s8.add(val[0] == p_set[i][0])
    #                             s8.add(val[1] == p_set[i][1])
    #                         elif (len(p_set[i]) == 3):
    #                             s8.add(val[0] == p_set[i][0])
    #                             s8.add(val[1] == p_set[i][1])
    #                             s8.add(val[2] == p_set[i][2])
    #                         elif (len(p_set[i]) == 4):
    #                             s8.add(val[0] == p_set[i][0])
    #                             s8.add(val[1] == p_set[i][1])
    #                             s8.add(val[2] == p_set[i][2])
    #                             s8.add(val[3] == p_set[i][3])
    #                         if s8.check() == sat:
    #                             flag8 = 1
    #                 if flag8 == 0:
    #                     clause.append(combine(1 * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #                     for j in range(self.n):
    #                         self.M[m][j] = 1
    #                     self.T[k][m] = True
    #                     self.Nt[k][m] = False
    #                     break
    #                 else:
    #                     clause.append(False)
    #                     self.T[k][m] = True
    #                     self.Nt[k][m] = True
    #                     # if fg == 0:
    #                     #     fg = 2
    #                     # status = (self.T[k][m], self.Nt[k][m])
    #                     # if status == (True, False):  # 选择取模
    #                     #     clause.append(
    #                     #         combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #                     # elif status == (False, True):
    #                     #
    #                     #     clause.append(
    #                     #         combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #                     # elif status == (True, True):
    #                     #     clause.append(False)
    #                     break
    #         # print(self.T[k][m], self.Nt[k][m], "222222222222222222222222222")
    #
    #     # print(clause, "Aaaaaaa/aaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
    #     if (len(clause) >1) and (False in clause):
    #         clause.remove(False)
    #
    #     # print(clause,"##########################3")
    #     formu.append(And(*clause))
    #
    #     print(formu)
    #     # print("simplify(Or(*formu))=\n",simplify(Or(*formu)))
    #     return simplify(Or(*formu))

    ########################################################################

    # def formula_model2(self , *val):  # 得到一个公式模型   kd：代入变量求得变量，代入数值就是求得一个值
    #     if len(val) == 0:
    #         val = self.vi
    #     formu = []
    #     for k in range(self.k):
    #         clause = []
    #         for h in range(self.h):
    #             Coe = combine(self.A[h][j] * val[j] for j in range(self.n))
    #             status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
    #             if status == (False, False, True):   #选择大于小于等于
    #                 clause.append(Coe <= self.B[h])
    #             elif status == (False, True, False):
    #                 clause.append(Coe >= self.B[h])
    #             elif status == (True, False, False):
    #                 clause.append(Coe != self.B[h])
    #             elif status == (False, True, True):
    #                 clause.append(Coe == self.B[h])
    #             elif status == (True, False, True):
    #                 clause.append(Coe < self.B[h])
    #             elif status == (True, True, False):
    #                 clause.append(Coe > self.B[h])
    #             elif status == (True, True, True):
    #                 clause.append(False)
    #         for m in range(self.m):
    #             status = (self.T[k][m], self.Nt[k][m])
    #             if status == (True, False):  #选择取模
    #                 clause.append(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] == self.C[m])
    #             elif status == (False, True):
    #                 clause.append(combine(self.M[m][j] * val[j] for j in range(self.n)) % self.E[m] != self.C[m])
    #
    #             elif status == (True, True):
    #                 clause.append(False)
    #         formu.append(And(*clause))
    #     # print("simplify(Or(*formu))=\n",simplify(Or(*formu)))
    #     return simplify(Or(*formu))

    def refine_modu(self, coe, e, b, res, tmp, last=0):
        # print(coe,e,b,res,tmp,last,"aaaaaaaaaaaaabbbbbb")
        if len(coe) == 1:
            if coe[0] == 0:
                if last % e == b:
                    tmp.append(0)
                else:
                    return
            for i in range(e):
                if (i + last) % e == b:
                    tmp.append(i)
                    break
            res.append(list(tmp))
            # print(tmp, "aaaaaaaaaaaaaaaaa")
            if (len(tmp)>0):
                tmp.pop()
            else:
                return
        elif coe[0] == 0:
            tmp.append(0)
            self.refine_modu(coe[1:], e, b, res, tmp, last)
            # print(tmp, "aaaaaaaaaaaaaaaaa")
            if (len(tmp)>0):
                tmp.pop()
            else:
                return
        else:
            for i in range(e):
                tmp.append(i)
                self.refine_modu(coe[1:], e, b, res, tmp, last + i)
                if (len(tmp) > 0):
                    tmp.pop()
                else:
                    return

    def build_formula(self, coe, V, e, C):
        # print(And(*[(coe[i] * v) % e == C[i] for i, v in enumerate(V)]))
        # print(V,C,coe,"@@@@@@@@@@@@@@@@@@@@@@@@@@@")
        expr = And(*[(coe[i] * v) % e == C[i] for i, v in enumerate(V)])
        return simplify(expr)

    def refine_model(self):
        formu_arr = []
        for k in range(1):
            clause = []
            for h in range(self.h):
                Coe = combine(self.A[h][j] * self.vi[j] for j in range(self.n))
                status = (self.He[k][h], self.Hge[k][h], self.Hle[k][h])
                # print(status,"222222222222222222222222222")
                if status == (False, False, True):
                    clause.append([Coe < self.B[h], Coe == self.B[h]])
                elif status == (False, True, False):
                    clause.append([Coe > self.B[h], Coe == self.B[h]])
                elif status == (True, False, False):
                    clause.append([Coe < self.B[h], Coe > self.B[h]])
                elif status == (False, True, True):
                    clause.append([Coe == self.B[h]])
                elif status == (True, False, True):
                    clause.append([Coe < self.B[h]])
                elif status == (True, True, False):
                    clause.append([Coe > self.B[h]])
                elif status == (True, True, True):
                    clause.append([False])
                # print(clause,"######################################")
            for m in range(self.m):
                status = (self.T[k][m], self.Nt[k][m])
                # print(status, "222222222222222222222222222")
                # Com = combine(self.M[m][j] * self.vi[j] for j in range(self.n))
                if status == (True, False):
                    # clause.append([Com % self.E[m] == self.C[m]])
                    mod_res = []

                    self.refine_modu(self.M[m], self.E[m], self.C[m], mod_res, [])
                    # print("mod_res!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!",mod_res)
                    for C in mod_res:
                        # print(self.M[m], self.vi, self.E[m], C)
                        clause.append([self.build_formula(self.M[m], self.vi, self.E[m], C)])
                elif status == (False, True):
                    mod_clause = []
                    for i in range(self.E[m]):
                        if i != self.C[m]:
                            # mod_clause.append(Com % self.E[m] == i)
                            mod_res = []
                            self.refine_modu(self.M[m], self.E[m], i, mod_res, [])
                            for C in mod_res:
                                mod_clause.append(self.build_formula(self.M[m], self.vi, self.E[m], C))
                    clause.append(mod_clause)
                elif status == (True, True):
                    clause.append([False])
                # print(clause, "######################################")
            # if (len(clause) > 1) and ([False] in clause):
            #     clause.remove([False])
            # print(clause,"111111111111111111111111111111111111111")
            formu_arr.append(clause)
        return formu_arr


class EquTemplate:
    def __init__(self, n):
        self.vi = [Int('v' + str(i)) for i in range(n)]
        self.b = Int('b')
        self.s = Solver()

    def add(self, vector):
        vi, target = vector[:-1], vector[-1]
        expr = combine(vi[i] * self.vi[i] for i in range(len(self.vi))) + self.b == target
        self.s.add(expr)

    def check(self):
        return self.s.check()

    def solve_model(self):
        model = self.s.model()
        V = [model[v].as_long() if model[v] is not None else 0 for v in self.vi]
        B = model[self.b].as_long() if model[self.b] is not None else 0
        expr = combine(V[i] * self.vi[i] for i in range(len(self.vi))) + B
        return simplify(expr)


if __name__ == '__main__':
    # smt = FormulaTemplate([Int('v1'), Int('v2')], 4, 3, 2)
    # smt.add([1, 2], True)
    # smt.add([2, 3], False)
    # print(smt.s)
    # print(smt.check())
    #
    # arr = smt.refine_model()
    # for a in arr:
    #     print(a)
    #
    # formu = smt.formula_model()
    # print(formu)
    # print('-' * 50)
    # print(simplify(formu))
    # print('-' * 50)

    smt = EquTemplate(2)
    smt.add([0, 1, 1])
    smt.add([1, 2, 1])
    smt.add([3, 6, 3])
    if smt.check() == sat:
        print(smt.solve_model())  # 1*v0 + 2*v1 + 1
    else:
        print(unsat)


