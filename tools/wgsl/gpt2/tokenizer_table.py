"""Offline table encoder shared by both GPT-2 artifact builders."""
import json
import unicodedata
import numpy as np


def pack_tokenizer(source, out):
    # Reconstruct OpenAI's byte-to-Unicode alphabet and merge ranks.
    alphabet = list(range(33,127))+list(range(161,173))+list(range(174,256))
    for b in range(256):
        if b not in alphabet:
            alphabet.append(b)
    n = 0
    characters = []
    for b in alphabet:
        if b in list(range(33,127))+list(range(161,173))+list(range(174,256)):
            characters.append(b)
        else:
            characters.append(256+n); n += 1
    byte_encoder = dict(zip(alphabet,map(chr,characters)))
    byte_decoder = {v:k for k,v in byte_encoder.items()}
    vocab = json.loads((source/'vocab.json').read_text())
    assert len(vocab) == 50257
    merge_offset = 264
    category_offset = merge_offset+2*131072
    decode_offset = category_offset+0x110000
    data_offset = decode_offset+50258
    table = [0x47505432,131072,merge_offset,category_offset,decode_offset,data_offset,0,0]
    table += [vocab[byte_encoder[b]] for b in range(256)]
    table += [0]*(2*131072)
    merges = [line.split() for line in (source/'merges.txt').read_text().splitlines()[1:] if line]
    assert len(merges) == 50000
    for rank, (a,b) in enumerate(merges):
        left,right,merged = vocab[a],vocab[b],vocab[a+b]
        assert merged == rank+256  # The Lean tokenizer compares these IDs as ranks.
        slot = (((left*65599)^right)*2654435761)&131071
        while table[merge_offset+2*slot]: slot = (slot+1)&131071
        table[merge_offset+2*slot:merge_offset+2*slot+2] = [left*65536+right+1,merged]
    for cp in range(0x110000):
        char = chr(cp); category = unicodedata.category(char)[0]
        # Unicode White_Space, as used by the GPT-2 regex (excludes C0 separators).
        space = cp in range(9,14) or cp in [32,133,160,5760,8232,8233,8239,8287,12288] or 8192 <= cp <= 8202
        table.append(3 if space else 1 if category == 'L' else 2 if category == 'N' else 0)
    decode_data, decode_starts = [], [0]
    for token,_ in sorted(vocab.items(), key=lambda item:item[1]):
        decode_data.extend(byte_decoder[c] for c in token)
        decode_starts.append(len(decode_data))
    table += decode_starts+decode_data
    np.asarray(table,dtype='<u8').tofile(out/'tokenizer.bin')
    return len(table), unicodedata.unidata_version
