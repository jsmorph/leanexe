import torch

from model import TinyGpt2


torch.set_num_threads(1)
torch.set_default_dtype(torch.float64)
torch.manual_seed(17)
for context in (4, 64, 128):
    model = TinyGpt2(context)
    assert sum(p.numel() for p in model.parameters()) == 2472 + 4 * context
    tokens = torch.randint(256, (2, context))
    output = model(tokens)
    assert output.shape == (2, context, 256)
    for length in (1, context // 2, context):
        prefix = model(tokens[:, :length])
        torch.testing.assert_close(prefix, output[:, :length], atol=1e-12, rtol=0)
    loss = torch.nn.functional.cross_entropy(output.reshape(-1, 256), tokens.reshape(-1))
    loss.backward()
    assert all(p.grad is not None and torch.isfinite(p.grad).all() for p in model.parameters())
    for length in (0, context + 1):
        try:
            model(torch.zeros((1, length), dtype=torch.long))
        except ValueError:
            pass
        else:
            raise AssertionError(f"Accepted invalid context length {length}")
    print(f"Checked context {context}: shapes, causal prefixes, gradients, and length rejection")
