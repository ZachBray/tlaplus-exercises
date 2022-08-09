# TLA+ exercises

Here are some (completed) exercises from [Lamport's TLA+ video lectures](https://www.youtube.com/channel/UCajiu4Cj_GHOX0if3Up-eRA/videos).

The layout is as follows:

```
.
├── container               -  Container definition for TLA+ tools
│   └── run.sh              -  Builds and runs the TLA+ container in interactive mode
└── src
    ├── diehard             -  Exercise to get exactly 4 units using 3 and 5 unit jugs
    ├── tx_commit           -  Abstract transaction commit specification and lower-level implementation
    └── alternating_bit     -  Abstract message transmission specification and lower-level implementation
```

### Notes

#### Configuration file syntax

The video lectures use the TLA+ Toolbox but I prefer to use the command line
tools. Instead of GUI-based configuration, this repository uses [TLC
configuration files](https://apalache.informal.systems/docs/apalache/tlc-config.html).

