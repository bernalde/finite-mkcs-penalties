#!/usr/bin/env python3
"""Build and compare this pilot with the genuine toolchain's independent kernels."""
from pathlib import Path
import argparse,datetime,hashlib,json,re,shutil,subprocess,time
ROOT=Path(__file__).resolve().parents[1]

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--evidence-dir',type=Path,required=True);args=parser.parse_args()
 out=args.evidence_dir.resolve();assert not out.exists(),'Preserve earlier verification attempts';out.mkdir(parents=True)
 for name in ['lake','lean','bwrap']:assert shutil.which(name),f'Missing required executable: {name}'
 prefix=Path(subprocess.check_output(['lean','--print-prefix'],cwd=ROOT,text=True).strip())
 config=json.loads((ROOT/'comparator.json').read_text());assert 'external_kernels'not in config
 for name in ['nanoda_bin','con-ron']:assert(prefix/'bin'/name).is_file(),name
 config['external_kernels']={name:[str(prefix/'bin'/exe)]for name,exe in [('nanoda','nanoda_bin'),('con-ron','con-ron')]}
 local=ROOT/'comparator-local.json';local.write_text(json.dumps(config,indent=2)+'\n')
 inputs={}
 for p in ROOT.rglob('*'):
  if not p.is_file()or'.lake'in p.relative_to(ROOT).parts:continue
  if p.suffix=='.lean'or p.name in ['lean-toolchain','lakefile.toml','lake-manifest.json','comparator.json']:
   inputs[p.relative_to(ROOT).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
 report={'state':'RUNNING','toolchain':(ROOT/'lean-toolchain').read_text().strip(),'lean_version':subprocess.check_output(['lean','--version'],text=True).strip(),'input_sha256':inputs,'steps':[],'no_service_submission':True}
 for name,argv in [('build',['lake','build']),('axioms',['lake','env','lean','AxiomAudit.lean']),('comparator',['lake','comparator','--config',str(local)])]:
  started=datetime.datetime.now(datetime.timezone.utc).isoformat();clock=time.monotonic()
  stdout=out/(name+'.stdout.txt');stderr=out/(name+'.stderr.txt')
  with stdout.open('xb')as a,stderr.open('xb')as b:r=subprocess.run(argv,cwd=ROOT,stdout=a,stderr=b)
  step={'name':name,'argv':argv,'started_utc':started,'elapsed_seconds':time.monotonic()-clock,'exit_code':r.returncode,'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256(stderr.read_bytes()).hexdigest()};report['steps'].append(step)
  if r.returncode:
   report['state']='FAILED';(out/'result.json').write_text(json.dumps(report,indent=2)+'\n');raise SystemExit(r.returncode)
  if name=='axioms':
   match=re.search(r"depends on axioms: \[([^]]*)\]",stdout.read_text());assert match,'No completed axiom census'
   axioms={s.strip()for s in match[1].split(',')if s.strip()};assert axioms<={'propext','Classical.choice','Quot.sound'},axioms;report['solution_axioms']=sorted(axioms)
 for name,digest in inputs.items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,('Input changed during verification',name)
 report['state']='PASS_REAL_BUILD_AXIOMS_SANDBOXED_COMPARATOR_AND_BUNDLED_KERNELS';(out/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(report['state'])
if __name__=='__main__':main()
