import homework
import os
import signal

def handler(signum, frame):
    raise Exception("timeout!")

signal.signal(signal.SIGALRM, handler)
signal.alarm(10)
for i in range(1,21):
    infile = './tests/test'+str(i)+'.txt'
    rubric_outfile = './tests/output'+str(i)+'.txt'
    my_outfile = './tests/my_out'+str(i)+'.txt'
    print('================'+infile+'================')
    try:
        my_sol = homework.Solver(infile)
        my_sol.solve(my_outfile)
        rubric_answers = []
        with open(rubric_outfile, 'r') as f:
            rubric_answers.append(f.readline().rstrip(' \n'))
        my_answers = []
        with open(my_outfile, 'r') as f:
            my_answers.append(f.readline().rstrip(' \n'))
        if rubric_answers == my_answers:
            print('OK')
            if os.path.exists(my_outfile):
                os.remove(my_outfile)
        else:
            print('???')
    except Exception, exc:
        print(exc)
