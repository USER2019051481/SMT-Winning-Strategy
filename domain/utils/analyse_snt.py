from z3 import And, Or, simplify


def analyse_snt_z3(word_list: list, mapper2z3):
    """
    参数1：输入一个列表，列表格式为[操作符，子句1，子句2]，表示一个语句
    子句可以是列表，也可以是表示单个元素的字符串
    参数2：自定义的转化函数，将变量"?v"转化为z3的占位符或者整数
    返回z3类型语句：子句1 操作 子句2
    """
    if type(word_list) == str:
        # print("!!!!!!!!!!!!word_list=",word_list)
        return mapper2z3(word_list)
    if word_list[0] == 'and':
        # print(" word_list=", word_list)
        expr = analyse_snt_z3(word_list[1], mapper2z3)
        # print("expr = ",expr)
        for i in range(2, len(word_list)):
            expr = And(expr, analyse_snt_z3(word_list[i], mapper2z3))
            # print("eeeee = ",expr)
    elif word_list[0] == 'or':
        # print(" word_list=", word_list)
        expr = analyse_snt_z3(word_list[1], mapper2z3)
        for i in range(2, len(word_list)):
            expr = Or(expr, analyse_snt_z3(word_list[i], mapper2z3))
    elif len(word_list) == 4 :
        # print("22222!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!12wwww", word_list)

        op = '=='
        num = '%'+word_list[2]
        # print(num)
        expr = eval("analyse_snt_z3(word_list[1], mapper2z3) %s %s analyse_snt_z3(word_list[3], mapper2z3)" %(num,op))
        # print("####################33" ,expr)

    else:
        # print("wwww",word_list)
        assert len(word_list) == 3



        op = word_list[0]
        # expr1 = analyse_snt_z3(word_list[1], mapper2z3)
        # expr2 = analyse_snt_z3(word_list[2], mapper2z3)
        op = "==" if op == '=' else op
        return eval("analyse_snt_z3(word_list[1], mapper2z3) %s analyse_snt_z3(word_list[2], mapper2z3)" % op)
    return simplify(expr)


def analyse_snt_bool(word_list: list, mapper2const):
    """
    参数1：输入一个列表，列表格式为[操作符，子句1，子句2]，表示一个语句
    参数2：自定义转化函数，将变量"?v"转化为python的基本数据类型
    返回语句的运算数值，可能是整数结果，也可能是bool类型结果
    """
    if type(word_list) == str:
        # print("test4",mapper2const(word_list))
        return mapper2const(word_list)
    if word_list[0] == 'and':
        # print("fsafafasf",word_list)
        expr = analyse_snt_bool(word_list[1], mapper2const)
        for i in range(2, len(word_list)):
            if not expr:
                return False
            expr = expr and analyse_snt_bool(word_list[i], mapper2const) #true
            # print("test4",expr)
    elif word_list[0] == 'or':
        expr = analyse_snt_bool(word_list[1], mapper2const)
        for i in range(2, len(word_list)):
            if expr:
                return True
            expr = expr or analyse_snt_bool(word_list[i], mapper2const)



    elif len(word_list) == 4 :
        op = '=='
        num = '%2'
        return eval("analyse_snt_bool(word_list[1], mapper2const) %s %s analyse_snt_bool(word_list[3], mapper2const)" %(num,op))
        # print("####################33" ,expr)

    else:
        # print("wfwfwfw",word_list)
        assert len(word_list) == 3
        op = word_list[0]
        val1 = analyse_snt_bool(word_list[1], mapper2const) #1
        val2 = analyse_snt_bool(word_list[2], mapper2const) #0
        # print("test4",val1)
        # print("test5",val2)
        op = "==" if op == '=' else op
        # print(eval("%s %s %s" % (val1, op, val2)))
        return eval("%s %s %s" % (val1, op, val2))
    return expr


if __name__ == "__main__":
    # 举个栗子
    # from domain.utils.split import split
    from  split import  split


    mapper = {"?v1": 6, "?v2": 5, "?k": 2}


    def mapper2const_(key):
        if key in mapper:
            return mapper[key]
        else:
            return int(key)


    word = "(or (and (>= ?v1 ?k) (= ?k 1)) (> ?v2 ?k))"
    word_list_ = split(word)
    print(word_list_)
    print(analyse_snt_bool(word_list_, mapper2const_))

    print("-" * 50)
    word = "(- ?v1 ?k)"
    word_list_ = split(word)
    print(word_list_)
    print(analyse_snt_bool(word_list_, mapper2const_))
