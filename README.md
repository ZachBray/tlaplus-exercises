# TLA+ specifications

Here are some specifications written in TLA+ and a docker container for running the TLC model checker.

The repository layout is as follows:

```
.
├── container               -  Container definition for TLA+ tools
│   └── run.sh              -  Builds and runs the TLA+ container in interactive mode
└── src
    ├── video_exercises     -  Exercises based on Lamport's video lectures
    └── own_problems        -  My own (various) specifications.
```

### Tools in the container

- `tlc $SPEC` runs the model checker on `$SPEC.tla` with the configuration in `$SPEC.cfg`
- `tla2pdf $SPEC` converts `$SPEC.tla` into a PDF document, `$SPEC.pdf`, via Latex
- `animate_tlc_trace $SPEC` converts the TLC trace output of a failing `$SPEC.tla` into an SVG-based animation in `$SPEC.html`
    - It expects the associated configuration `$SPEC.cfg` to define a `VIEW` where that `VIEW` maps each state onto an SVG group. See `src/own_problems/StateTransferAnimated.tla` for example.

### Useful links

#### Videos

- [Lamport's TLA+ video lectures](https://www.youtube.com/channel/UCajiu4Cj_GHOX0if3Up-eRA/videos)
- [Dr TLA+ series](https://github.com/tlaplus/DrTLAPlus)

#### Community

- [Lamport's TLA+ website](https://lamport.azurewebsites.net/tla/tla.html)
- [TLA+ google group](https://groups.google.com/g/tlaplus)
- [TLA+ community-provided modules](https://github.com/tlaplus/CommunityModules)
- [TLA+ examples](https://github.com/tlaplus/Examples)

#### Configuration syntax

- [TLC configuration file syntax](https://apalache.informal.systems/docs/apalache/tlc-config.html)

#### Tools/utilities

- [TLA+ web-based behaviour explorer](https://github.com/will62794/tla-web)
- [TLA+ behaviour animations](https://github.com/will62794/tlaplus_animation)

