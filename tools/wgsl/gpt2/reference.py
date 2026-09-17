#!/usr/bin/env python3
"""Independent offline reference checks; never imported by an inference runner."""
from pathlib import Path
import argparse
import json
import subprocess
import random
import numpy as np
import torch
from transformers import GPT2Tokenizer, GPT2LMHeadModel

parser = argparse.ArgumentParser()
parser.add_argument('--source',type=Path,default=Path('build/gpt2/source'))
parser.add_argument('--output',type=Path,default=Path('build/gpt2/reference.json'))
parser.add_argument('--prompt',default='The purpose of science is')
parser.add_argument('--logits',type=Path)
parser.add_argument('--skip-tokenizer',action='store_true')
parser.add_argument('--trace',type=Path)
parser.add_argument('--temperature',type=float,default=0)
parser.add_argument('--seed',type=int,default=42)
args = parser.parse_args()
torch.set_num_threads(2)
tokenizer = GPT2Tokenizer.from_pretrained(args.source,local_files_only=True)
cases = [args.prompt,"Hello, world!","I'm not sure; we've tried it twice.",
    ' a  b   c\n\nNext\tword\n', '123.456 — café 日本語 🧠',"They'll say: 'it's fine'.",' trailing  ',
    'a\u00a0b\u2003c','A\r\n B\t C', 'x\x1cy']
rng = random.Random(1729)
pieces = ['Hello','world',"'s","'ll",' ', '\r', '\n', '\t', ' café', '日本語', '🧠', '!?', '123', '\u00a0']
cases += [''.join(rng.choices(pieces,k=8)) for _ in range(40)]
tokenization = []
for text in ([] if args.skip_tokenizer else cases):
    expected = tokenizer.encode(text,add_special_tokens=False)
    process = subprocess.run(['tools/gpt2','run','--tokenize',text],text=True,capture_output=True,check=True)
    actual = [int(x) for x in process.stdout.strip().split(',')]
    assert actual == expected,(text,expected,actual)
    tokenization.append({'text':text,'tokens':actual})
print(f'Tokenizer: {len(tokenization)} independent cases match',flush=True)
model = GPT2LMHeadModel.from_pretrained(args.source,local_files_only=True,attn_implementation='eager').eval()
inputs = tokenizer(args.prompt,return_tensors='pt')
with torch.no_grad():
    reference = model(**inputs).logits[0,-1].numpy()
    generated = model.generate(**inputs,max_new_tokens=32,do_sample=False,pad_token_id=50256)
result = {'prompt':args.prompt,'tokenization':tokenization,
    'referenceTop10':np.argsort(reference)[-10:][::-1].tolist(),
    'referenceGreedy':tokenizer.decode(generated[0])}
if args.logits:
    actual = np.fromfile(args.logits,dtype='<f8')
    assert actual.shape == reference.shape and np.isfinite(actual).all()
    error = abs(actual-reference.astype(np.float64))
    result.update(maxAbsoluteLogitError=float(error.max()),meanAbsoluteLogitError=float(error.mean()),
        actualTop10=np.argsort(actual)[-10:][::-1].tolist())
    assert result['actualTop10'] == result['referenceTop10'], result
    assert error.max() < 0.005,result
if args.trace:
    records = np.fromfile(args.trace,dtype='<u8').reshape(-1,50258)
    chosen = records[:,0].astype(np.int64)
    actual = records[:,1:].copy().view('<f8')
    sequence = torch.tensor([tokenizer.encode(args.prompt)+chosen[:-1].tolist()])
    with torch.no_grad():
        expected = model(sequence).logits[0,inputs.input_ids.shape[1]-1:].numpy().astype(np.float64)
    error = abs(actual-expected)
    result['trace'] = {'steps':len(chosen),'chosenTokens':chosen.tolist(),
        'maximumErrorPerStep':error.max(axis=1).tolist(),
        'actualGreedy':actual.argmax(axis=1).tolist(),'referenceGreedy':expected.argmax(axis=1).tolist(),
        'decoded':tokenizer.decode(sequence[0].tolist()+[int(chosen[-1])])}
    args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(result['trace'],indent=2),flush=True)
    assert np.isfinite(actual).all() and error.max() < 0.005,result['trace']
    state = args.seed
    for i, row in enumerate(actual):
        if args.temperature == 0:
            selected = int(row.argmax())
        else:
            # Independent reference for the specified top-k ordering and RNG.
            values, indices = row[:40].copy(), list(range(40))
            minimum = int(values.argmin())
            for token in range(40,len(row)):
                if row[token] > values[minimum]:
                    values[minimum] = row[token]; indices[minimum] = token
                    minimum = int(values.argmin())
            state ^= state >> 12
            state = (state ^ (state << 25)) & ((1<<64)-1)
            state ^= state >> 27
            random_word = (state*0x2545F4914F6CDD1D) & ((1<<64)-1)
            uniform = (random_word >> 12)/(1<<52)
            weights = np.exp((values-values.max())/args.temperature)
            target = uniform*weights.sum()
            selected = indices[min(int(np.searchsorted(weights.cumsum(),target,side='right')),39)]
        assert selected == int(chosen[i]),('sampler',i,selected,int(chosen[i]))
    result['trace']['samplerChecks'] = len(chosen)
args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='tokenization'},indent=2,ensure_ascii=False))
