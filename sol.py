import ceeflp as d
import time,sys,random,math
nf=0
mincap=0
max_fcost=0.0
avg_dis=1.0
alpha=1.0
psize=10 #population size
maxloops=100 #max_loops_solution_not_improved
tlimit=3600 #timelimit for searching
filetype=0

if len(sys.argv) >= 2:
    fn=sys.argv[1]
if len(sys.argv) >= 3:
    filetype=int(sys.argv[2])
if len(sys.argv) >= 4:
    max_fcost=float(sys.argv[3])
if len(sys.argv) >= 5:
    avg_dis=float(sys.argv[4])
if len(sys.argv) >= 6:
    alpha=float(sys.argv[5])
if len(sys.argv) >= 7:
    psize=int(sys.argv[6])
if len(sys.argv) >= 8:
    maxloops=int(sys.argv[7])
d.facilityMinimumCapacity=mincap
d.max_facility_cost=max_fcost
d.facilityMaximumCapacity=0#100000
d.location_problem=4 #uflp

#How to set model parameters？----------------------------------
#problem objective          uflp    flp_efficiency  flp_equality
#max_fcost                  0       maxFacilityCost maxFacilityCost
#avg_dis                    ~       ~               d=meanDistance
#alpha                      1       1               0.001 or var/(var+2d)
#d.fixed_cost_obj           1       0               0
#d.envy_service_objective   0       0               1

d.distance_type=0
d.fixed_cost_obj=0 
d.travel_distance_weight=alpha
d.envy_service_objective=1
d.envy_service_distance=avg_dis
d.envy_objective_weight=1-alpha

d.max_num_facility=nf
d.adaptive_number_of_facilities=01
d.pop_dis_coeff=100000#10000#1000000 #100000 for FLP 1-5 for PDP
d.pop_deviation=0.0 #for PDP
d.max_loops_solution_not_improved=maxloops #for search termination
d.is_spp_modeling=0
d.distance_type=0
fn2="na"

t0=time.time()
if filetype==0: #geo
    d.readfile(fn,fn2) #read self-defined instances
if filetype==1: # CPMP or FLP instances
    d.read_cpmp_file(fn)
if filetype==2: #pmed instances
    d.read_pmp_or_instance(fn)
if filetype==3: #tbed instances     
    d.read_bm_instance2(fn) #read tbed instances
if filetype==4: #or-lib,holmberge,yang instance
    d.read_bm_instance(fn) 
if filetype==5: #demand file f_ and supply file f2
    fn1=fn+"_demand.txt"
    fn2=fn+"_supply.txt"
    d.readfile_ab(fn1,fn2,"")

d.solver_message=01
d.mip_solver="cplex"#"gurobi"
d.me_uflp_model(tlimit,0.000000001)
#d.ils_pmp_envy(nf,psize,tlimit,-1)

d.search_stat()
print "=========================Final results========================="
print "objective:",d.biobjective
print "facility cost",d.objective_fcost
print "transportation cost:",d.objective
print "srrvice overload", d.objective_overload
print "pool size",len(d.region_pool)
print "total time",time.time()-t0
print "facilities selected",[x for x in d.centersID if x>=0]
print "demand assignment:", d.node_groups
print "service area stat:"
for i in range(d.num_districts):
    if d.district_info[i][0]==0: continue
    print d.facilityCandidate[i],d.district_info[i], d.district_info[i][2]/d.district_info[i][1]
d.update_envy_district_info()
d.search_stat()
sol=d.sol_stat()
print "=========================Objectives========================="
for x in sol:
    print x,sol[x]

equality_measures=d.print_equality_measures()
print "-----------equality measures---------------"
for x in equality_measures:
    print  x,equality_measures[x]
d.coverage_stat()
print "CPU_time",time.time()-t0