"""The validator's long-running processes, each wired here and pure underneath.

    cd validator && python -m workers.chain_watcher    subnet registrations -> the store
    cd validator && python -m workers.weight_setter    the store -> a weight vector

The gate worker lives beside the API it shares settings with, as `service.worker`.
"""
