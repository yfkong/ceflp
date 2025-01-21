A cost-efficient and equitable facility location problem: model, algorithm, and benchmark analysis

How to solve an instance using my algorithm?
pypy sol.py instance format MaxCost d* weight popsize mloops
instance: instance file name
format: instance file format (0 self-defined, 1 flp, 2 pmed, 3 tbed, 4 OR-Lib yang, 5 demand and supply)
MaxCost: maximum facility cost (0 no constraint on cost)
d*: threshold envy distance (mean distance)
weight: weight on distance (1 for uflp and spatail efficiency, 0~0.9999 for equality)
popsize: popluation size (10)
mloops: maxsimum loops that the best solution is not updated (100)

1 CFLP
d.fixed_cost_obj=1
...\pypy sol.py ...\geo_zy.txt 0 0 0 1 10 100

2 Minimizing totol travel distance only
d.fixed_cost_obj=0 
d.envy_service_objective=0
...\pypy sol.py ...\geo_zy.txt 0 2000 0 1 10 100

3 Minimizing spatial inequality
d.fixed_cost_obj=0 
d.envy_service_objective=1
...\pypy sol.py ...\geo_zy.txt 0 2000 0.4 0.001 10 100

How to solve an instance using MIP optimizer?
d.me_uflp_model(tlimit,0.000000001)
