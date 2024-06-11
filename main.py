from my_verificator import Verificator
from my_parser import check
inp = open('input.txt')

nochoice = False
choice = '0'
if not nochoice:
    choice = input("Если хотите выполнять ввод из файла 'input.txt', то введите 0. Иначе ввод будет выполняться в консоли")
if choice != '0':
    verificator = Verificator()
    verificator.run()
else:
    with open('input.txt') as inp:
        l = True
        steps = []
        while l:
            l = inp.readline()
            if l == '\n' or not l:
                continue
            steps.append(l.replace('\n', ''))
            # print(l.__repr__())
        print(steps[0].__repr__(), check(steps[0]))
        verificator = Verificator(steps[0], steps[1:])
        printlist = verificator.run(True)
    printtext = ''
    for p in printlist:
        printtext += p + '\n'
    myfile = open('output.txt', 'w')
    myfile.write(printtext)
    myfile.close()