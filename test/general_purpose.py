#!/usr/bin/env python3
"""Independent standard-library, effects, handle and attribute acceptance."""
import argparse, ast, itertools, json, os, random, re, socket, subprocess, tempfile, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def require(ok, detail):
    if not ok: raise AssertionError(detail)

class Tests:
    def __init__(self, binary, directory, env):
        self.binary, self.dir, self.env = binary, directory, env
        self.n = 0
    def execute(self, source, *args, code=0, stdin='', run=True, timeout=15):
        self.n += 1
        p = self.dir / f'test{self.n}.nprolog'; p.write_text(source)
        result = subprocess.run([str(self.binary), *(['run'] if run else []), str(p), *args],
                                input=stdin if run else ':quit\n', text=True, capture_output=True,
                                cwd=self.dir, env=self.env, timeout=timeout)
        require(result.returncode == code, (source,result.returncode,result.stdout,result.stderr))
        return result
    def pure(self, source, goal, expected):
        p = self.execute(source+'\nprobe Result <- '+goal+'.\n> probe Result?\n',run=False)
        require('Error:' not in p.stdout and 'Error:' not in p.stderr, p)
        lines = re.findall(r'^Result = (.+)$', p.stdout,re.M)
        require(lines == [expected], (goal,expected,p.stdout))
    def check(self, source, error=False):
        self.n += 1; p=self.dir/f'check{self.n}.nprolog';p.write_text(source)
        result=subprocess.run([str(self.binary),'check','--json',str(p)],text=True,capture_output=True,cwd=self.dir,env=self.env)
        rows=json.loads(result.stdout)['diagnostics']
        require(any(x['severity']=='error' for x in rows)==error,(source,rows))
    def main(self, body, extra=''):
        return 'main : io.\nmain _ -> '+body+'.\n'+extra


def library(t):
    rng=random.Random(2461)
    for _ in range(30):
        xs=[rng.randrange(-10,11) for _ in range(rng.randrange(0,15))]
        literal=json.dumps(xs)
        t.pure('',f'reverse {literal} Result',str(xs[::-1]))
        t.pure('',f'msort {literal} Result',str(sorted(xs)))
        t.pure('',f'sort {literal} Result',str(sorted(set(xs))))
        t.pure('',f'sum_list {literal} Result',str(sum(xs)))
        t.pure('',f'findall N (nth0 N {literal} _) Result',str(list(range(len(xs)))))
    t.pure('','length Result 4, Result = [a,b,c,d]','[a, b, c, d]')
    t.pure('member x [x].','findall X (member X [a,b]) Result','[]')
    t.pure('<- noprelude.\np a.','findall H (clause H true) Result','[p a]')
    t.pure('odd N <- R is N % 2, R = 1.','partition odd [1,2,3,4] A B, Result = [A,B]','[[1, 3], [2, 4]]')
    t.pure('add X A B <- B is X + A.','foldl add [1,2,3] 0 Result','6')
    choices = 'pick X _ X.\npick _ A A.'
    t.pure(choices, 'findall R (foldl pick [1,2] 0 R) Result', '[2, 1, 2, 0]')
    t.pure(choices, 'foldl pick [] A B, A == B, Result = yes', 'yes')
    t.pure(choices, 'findall R (foldl pick [1|bad] 0 R) Result', '[]')
    t.pure('foldl _ _ _ shadow.\nadd X A B <- B is X + A.',
           'foldl add [1,2] 0 Result', 'shadow')
    t.pure(choices + '\nrun F L A R <- foldl F L A R.',
           'findall R (run pick [1,2] 0 R) Dynamic, '
           'findall R (foldl pick [1,2] 0 R) Static, Static == Dynamic, Result = ok', 'ok')
    t.pure('plus K X A B <- B is A + X + K.',
           'foldl (plus 10) [1,2] 0 Result', '23')
    t.pure('first : unsafe.\nprobe : unsafe.\nfirst X _ X <- !.\nfirst _ A A.',
           'findall R (member S [0,1], foldl first [2] S R) Result', '[2, 2]')
    t.pure('dup : table.\ndup X _ X.\ndup X _ X.',
           'findall R (foldl dup [a] z R) Result', '[a]')
    t.pure('keep X _ X.', 'foldl keep [A,B] z R, R == B, var A, Result = ok', 'ok')
    t.pure('p a 2.\np b 1.\np a 1.\np a 2.', 'findall (pair K B) (bagof X (p K X) B) Result','[pair a [2, 1, 2], pair b [1]]')
    t.pure('p a 2.\np b 1.\np a 1.\np a 2.', 'setof X (K ^ (p K X)) Result','[1, 2]')
    t.pure('p K K.\np K (box K).', 'bagof T (p K T) [A,box B], A == B, Result = yes', 'yes')
    t.pure('','aggregate_all count (between 1 8 _) Result','8')
    t.pure('','keysort [pair b 0,pair a 1,pair a 2] Result','[pair a 1, pair a 2, pair b 0]')
    assoc='<- import "std/assoc".\n'
    for _ in range(20):
        pairs=[(rng.randrange(10),rng.randrange(50)) for _ in range(20)]
        src='['+','.join(f'pair {k} {v}' for k,v in pairs)+']'
        want='['+', '.join(f'pair {k} {v}' for k,v in sorted(dict(pairs).items()))+']'
        t.pure(assoc,f'list_to_assoc {src} A, assoc_to_list A Result',want)
    t.pure('<- import "std/str".','split "a::b::" "::" Result','["a", "b", ""]')
    t.pure('<- import "std/str".','join ["a","b","c"] "," Result','"a,b,c"')
    t.pure('<- import "std/str".','trim " \t abc \n" Result','"abc"')
    t.n+=1
    shown=subprocess.run([str(t.binary)],input=':sig seq\n:sig str_concat\n:sig copy_term_nat\n:quit\n',text=True,capture_output=True,cwd=t.dir,env=t.env)
    require(all(name+' :' in shown.stdout for name in ['seq','str_concat','copy_term_nat']),shown)
    t.check('bad Bag <- bagof X (write X) Bag.\n', True)
    t.check('bad Bag <- setof X (Y ^ (missing X Y)) Bag.\n', True)
    for name in ['list','order','aggregate','assoc','str','dcg','io','net','os','coroutine']:
        t.check(f'<- import "std/{name}".\n')

def attributes(t):
    # A dynamically constructed name must still trigger the safe interpreter
    # fallback even if no hook or attribute builtin was spelled in the source.
    t.pure('', 'str_concat "put_" "attr" S, str_atom S F, call F X missing_module yes, Result = yes', 'yes')
    src='<- import "std/coroutine".\n'
    t.pure(src,'freeze X (is Y 7), X = ready, Result = [X,Y]','[ready, 7]')
    t.pure(src,'findall [X,Y] (dif X Y, member X [0,1], member Y [0,1]) Result','[[0, 1], [1, 0]]')
    t.pure(src,'when (ground (pair X Y)) (is Z 7), X = a, Y = b, Result = Z','7')
    t.pure(src,'freeze X (is Y 1), (X = a, fail ; X = b), Result = [X,Y]','[b, 1]')
    demo=src+'demo:attr_unify_hook V Other <- (var Other -> put_attr Other demo V ; V = Other).\n'
    t.pure(demo,'put_attr X demo a, copy_term (box X X) (box Y Y), get_attr Y demo a, Y = a, var X, Result = yes','yes')
    t.pure(demo,'put_attr X demo a, copy_term_nat X Y, not (get_attr Y demo _), Result = yes','yes')
    t.pure(demo,'put_attr X demo a, (del_attr X demo, fail ; get_attr X demo a), Result = yes','yes')
    t.pure(src,'freeze X (is N 1), when (ground (pair X Y)) (is M 2), X = a, Y = b, Result = [N,M]','[1, 2]')
    dpll=(ROOT/'examples/dpll.nprolog').read_text().split('\n> ')[0]
    rng=random.Random(917)
    for _ in range(30):
        n=3; clauses=[[(rng.randrange(n),rng.randrange(2)) for _ in range(rng.randrange(0,4))] for _ in range(rng.randrange(0,6))]
        names=['X','Y','Z']
        formula='['+','.join('['+','.join(f'lit {names[v]} {pol}' for v,pol in c)+']' for c in clauses)+']'
        want=[list(bits) for bits in itertools.product([0,1],repeat=n) if all(any(bits[v]==pol for v,pol in c) for c in clauses)]
        t.pure(dpll,f'findall [X,Y,Z] (sat {formula} [X,Y,Z]) Result',str(want))

def effects(t):
    t.execute(t.main('say "hello\\n"'),code=0)
    t.execute(t.main('{ fail }'),code=1)
    p=t.execute(t.main('{ X is 1 / 0 }'),code=2);require('Fault:' in p.stderr and 'division by zero' in p.stderr,p)
    t.execute(t.main('halt 7'),code=7)
    # Inline queries are never executed by infera run.
    p=t.execute(t.main('say "only-main\\n"')+'\n> write "inline"?');require(p.stdout=='only-main\n',p)
    t.check('main : io.\nmain A W0 W <- open (string "") read R W0 W1, close R W0 W.\n',True)
    t.check('bad X Y Z <- open (file "x") read X Y Z.\n',True)
    t.check('main : io.\nmain _ -> { findall X (open (file "x") read X A B) _ }.\n',True)
    p=t.execute(t.main('{ member X [a,b] }, say (fmt "~w" [X])'),code=2);require('backtracking' in p.stderr,p)
    p=t.execute(t.main('say "before\\n", { member X [a,b] }'),code=2);require('backtracking' in p.stderr,p)
    p=t.execute(t.main('open (string "abc") read (ok H), close H, close H'),code=2);require('closed' in p.stderr,p)
    p=t.execute(t.main('open (file "missing-unique-file") read R, say (fmt "~w" [R])'));require('err enoent' in p.stdout,p)
    body='open (string Text) write (ok H), say_to H "αβ", close H, open (string Text) read (ok R), read_chars R 2 Chars, close R, { Chars = ok Value }, say Value'
    p=t.execute(t.main(body));require(p.stdout=='αβ',p)
    # On-demand parsing returns without waiting for EOF and retains read-ahead.
    extra='one C -> [C].\n'
    p=t.execute(t.main('open (string "ab\\ncd") read (ok H), phrase_from H (one C), read_line H R, say (fmt "~w ~w" [C,R]), close H',extra))
    require(p.stdout=="'a' ok \"b\"",p)
    target=t.dir/'out.txt'
    p=t.execute(t.main(f'open (file {json.dumps(str(target))}) write (ok H), say_to H "saved", close H'))
    require(target.read_text()=='saved',p)
    wc=ROOT/'examples/wc.nprolog'
    text='one two\nthree λ\nlast'
    target.write_text(text)
    p=subprocess.run([str(t.binary),'run',str(wc),str(target)],text=True,capture_output=True,cwd=t.dir,env=t.env)
    require(p.returncode==0 and p.stdout==f'{text.count(chr(10))} {len(text.split())} {len(text)}\n',p)
    p=t.execute(t.main('open (string "ab\\n") read (ok H), phrase_from H prefix, read_line H R, say (fmt "~w" [R]), close H', 'prefix -> "a", ("x" -> [] ; []).\n'))
    require(p.stdout=='ok "b"',p)
    t.execute(t.main('open (string "a") read (ok H), phrase_from H wanted, close H','wanted -> "z".\n'),code=1)
    root=t.dir/'managed-dir'; a=root/'a'; b=root/'b'
    body=f'make_dir {json.dumps(str(root))} ok, open (file {json.dumps(str(a))}) (binary write) (ok H), write_bytes H [0,255,10,128] ok, close H, rename {json.dumps(str(a))} {json.dumps(str(b))} ok, stat {json.dumps(str(b))} (ok (stat file 4)), list_dir {json.dumps(str(root))} (ok Names), open (file {json.dumps(str(b))}) (binary read) (ok R), read_bytes R 4 (ok Bs), close R, remove {json.dumps(str(b))} ok, say (fmt "~w ~w" [Names,Bs])'
    p=t.execute(t.main(body));require(p.stdout=='["b"] [0, 255, 10, 128]',p)
    p=t.execute(t.main('now T, monotonic A, sleep 1, monotonic B, { B >= A, T > 0 }, getenv "INFERA_MISSING_ENV_TEST" Missing, say (fmt "~w" [Missing])'))
    require(p.stdout=='err enoent',p)
    p=t.execute('> say "inline\\n"?\n',run=False);require('inline\n' in p.stdout,p)
    for name,stdin,stdout,stderr in [
        ('lisp','(plus 2 (times 3 4))\n','14\n',''),
        ('log_report','','sum: 6\n','visiting 1\nvisiting 2\nvisiting 3\n'),
        ('wc','one two\nlast', '1 3 12\n','')]:
        t.n+=1
        p=subprocess.run([str(t.binary),'run',str(ROOT/'examples'/(name+'.nprolog'))],input=stdin,text=True,capture_output=True,cwd=t.dir,env=t.env,timeout=10)
        require(p.returncode==0 and p.stdout==stdout and p.stderr==stderr,p)
    # Pure random state is reproducible.
    t.pure('<- import "std/os".','random 1 S Result','1015568748')


def network(t):
    # Real loopback, including two simultaneously connected clients for wait.
    p=subprocess.Popen([str(t.binary),'run',str(ROOT/'examples/http_hello.nprolog'),'0'],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=t.dir,env=t.env)
    try:
        line=p.stdout.readline(); match=re.search(r'(\d+)\s*$',line.strip());require(match is not None,line)
        with socket.create_connection(('127.0.0.1',int(match.group(1))),timeout=5) as s:
            s.sendall(b'GET / HTTP/1.1\r\nHost: localhost\r\n\r\n')
            data=b''
            while True:
                chunk=s.recv(4096)
                if not chunk:break
                data+=chunk
        require(data.endswith(b'hello\n') and b'200 OK' in data,data)
        require(p.wait(timeout=5)==0,p.stderr.read())
    finally:
        if p.poll() is None:p.kill();p.wait()
    p=subprocess.Popen([str(t.binary),'run',str(ROOT/'examples/chat.nprolog'),'0'],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=t.dir,env=t.env)
    try:
        line=p.stdout.readline();port=int(re.search(r'(\d+)\s*$',line.strip()).group(1))
        with socket.create_connection(('127.0.0.1',port),timeout=5) as a, socket.create_connection(('127.0.0.1',port),timeout=5) as b:
            for i in range(4):
                src,dst=(a,b) if i%2==0 else (b,a)
                message=f'message-{i}\n'.encode();src.sendall(message);require(dst.recv(100)==message,'chat readiness relay')
        require(p.wait(timeout=5)==0,p.stderr.read())
    finally:
        if p.poll() is None:p.kill();p.wait()
    # A late third client is registered before relaying, and the relay ends
    # only when the last client leaves.
    t.n+=1
    p=subprocess.Popen([str(t.binary),'run',str(ROOT/'examples/chat.nprolog'),'0'],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=t.dir,env=t.env)
    try:
        line=p.stdout.readline();port=int(re.search(r'(\d+)\s*$',line.strip()).group(1))
        a=socket.create_connection(('127.0.0.1',port),timeout=5); b=socket.create_connection(('127.0.0.1',port),timeout=5)
        a.sendall(b'one\n');require(b.recv(100)==b'one\n','chat first relay')
        c=socket.create_connection(('127.0.0.1',port),timeout=5)
        # c joined before this line was sent, so it receives it too.
        b.sendall(b'hello\n');require(a.recv(100)==b'hello\n' and c.recv(100)==b'hello\n','chat relay to early and late clients')
        c.sendall(b'late\n');require(a.recv(100)==b'late\n' and b.recv(100)==b'late\n','chat relay from a late client')
        a.close();b.sendall(b'two\n');require(c.recv(100)==b'two\n','chat after a client left')
        b.close();c.close()
        require(p.wait(timeout=5)==0,p.stderr.read())
    finally:
        if p.poll() is None:p.kill();p.wait()
    # A fault must close its listening socket before the process exits.
    t.n+=1;path=t.dir/'fault-socket.nprolog'
    path.write_text(t.main('open (listen "127.0.0.1" 0) update (ok L), handle_address L A, say (fmt "~w\\n" [A]), { X is 1 / 0 }'))
    p=subprocess.run([str(t.binary),'run',str(path)],text=True,capture_output=True,cwd=t.dir,env=t.env,timeout=10)
    require(p.returncode==2 and str(path) in p.stderr,p)
    port=int(re.search(r'(\d+)\s*$',p.stdout.strip()).group(1))
    with socket.socket(socket.AF_INET,socket.SOCK_STREAM) as probe:
        probe.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1);probe.bind(('127.0.0.1',port))
    # UDP echo through the same handle registry.
    source=t.main('open (udp 0) update (ok H), handle_address H Address, say (fmt "~w\\n" [Address]), recv_from H 100 (ok (packet Peer Bytes)), send_to H Peer Bytes ok, close H')
    t.n+=1;path=t.dir/'udp.nprolog';path.write_text(source)
    p=subprocess.Popen([str(t.binary),'run',str(path)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=t.dir,env=t.env)
    try:
        line=p.stdout.readline();port=int(re.search(r'(\d+)\s*$',line.strip()).group(1))
        with socket.socket(socket.AF_INET,socket.SOCK_DGRAM) as s:
            s.settimeout(5);s.sendto(b'udp-bytes\x00\xff',('127.0.0.1',port));data,_=s.recvfrom(100)
        require(data==b'udp-bytes\x00\xff',data);require(p.wait(timeout=5)==0,p.stderr.read())
    finally:
        if p.poll() is None:p.kill();p.wait()
    # Unix-domain client, served by an independent Python process.
    sockpath=str(t.dir/'socket')
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as listener:
        listener.bind(sockpath);listener.listen()
        source=t.main(f'open (unix {json.dumps(sockpath)}) update (ok H), say_to H "hello\\n", read_line H R, say (fmt "~w" [R]), close H')
        path=t.dir/'unix.nprolog';path.write_text(source)
        p=subprocess.Popen([str(t.binary),'run',str(path)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=t.dir,env=t.env)
        try:
            listener.settimeout(5)
            peer,_=listener.accept()
            with peer:
                require(peer.recv(100)==b'hello\n','unix request');peer.sendall(b'world\n')
            out,err=p.communicate(timeout=5);require(p.returncode==0 and out=='ok "world"',(out,err))
        finally:
            if p.poll() is None:p.kill();p.wait()


def main():
    ap=argparse.ArgumentParser();ap.add_argument('binary',type=Path);ap.add_argument('--all-modes',action='store_true');args=ap.parse_args()
    modes=[('0','0'),('0','1'),('1','0'),('1','1')] if args.all_modes else [('1','1')]
    for jit,stream in modes:
        with tempfile.TemporaryDirectory(prefix='infera-general-') as d:
            t=Tests(args.binary.resolve(),Path(d),{**os.environ,'INFERA_JIT':jit,'INFERA_CORE_STREAM':stream})
            library(t);attributes(t);effects(t);network(t)
            print(json.dumps({'status':'ok','jit':jit,'stream':stream,'checks':t.n}),flush=True)
if __name__=='__main__':main()
