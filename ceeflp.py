# -*- coding: utf-8 -*-
## An unified algorithm framework for the Facility Location, Allocation, Service Area, and Regionalization Problems. 
## yfkong@henu.edu.cn, Dec.,2024
## to solve problems such as:
## 1 TP, GAP,SAP
## 2 SSCFLP, SSCKFLP, CFLSAP, CKFLSAP
## 3 PMP/CPMP
## 4 PCP
## 5 Eaqul districting problrms
## 6 DCCFLP:CFLP with maximum covering radius and covering percentage
## 7 extended PMP, CPMP with inequity inverse objective
## 8 extended UFLP, CFLP with cost-enquity-assessibility objectives and their variants
## 9 uncapaitiated and capacitated PCP, k-centrum, alha-centdian, k-centdian problems
## 10 MinSD, MinMAD, MinAD, MinCV, MinSI, MinGC location problems
## 11 Regionalization problem using multi-attibutes with atribute weights and areal weight
## 12 2SFCA
 
import sys,os,random,time,copy,math,tempfile
#ArcGIS
has_arcpy=0
try:
	import arcpy
	has_arcpy=1
except:
	has_arcpy=0
#mip solver
mip_solvers=[] #MIP solvers supported 
mip_solver=''  #MIP solver, "cplex", "cbc" or ""
mip_file_path=tempfile.gettempdir()
os.chdir(mip_file_path)	 #used in arcgis
try:
	import cplex
	#mip_solvers.append('cplex')
except: 
	pass
try:
	import pulp
	s=pulp.apis.GUROBI_CMD()
	if s.available()==False:
		pass
	else:
		mip_solvers.append('gurobi')
	s=pulp.apis.cplex_api.CPLEX_CMD()
	if s.available()==False:
		pass
	else:
		mip_solvers.append('cplex')
	s=pulp.apis.COIN_CMD()
	if s.available()==False:
		pass
	else:
		mip_solvers.append('cbc')
except: 
	pass
if len(mip_solvers)>0: mip_solver=mip_solvers[0]

#constant
MAXNUMBER=1.0e+20
MINNUMBER=1.0e-10
bigM=10000.0

#instance info
nodes=[]
nodes_std=[] #for homoDP only
weight_features=[] #for homoDP only
num_units=-1
nodedij=[]
nodedik=[]	#weighted cost from i to k, =nodedij*nodes[][3] 
nodendij=[] #network distance
node_neighbors=[]
facility_neighbors=[]
total_pop=0
avg_pop=0
total_supply=0
distance_type=0 #0 Euclidean, 1 Manhattan, 2 Geo 3 Network
all_units_as_candadate_locations=0
facilityCandidate=[] #attribute = 0,1,2...
facility_inclusion_list=[] #attribute = 1
facility_inclusion_list2=[] #attribute = 1

facilityCapacity=[]
facilityMinimumCapacity=0
facilityMaximumCapacity=0
facilityCost=[]
num_facilityCandidate=-1
num_districts=-1 # number of service areas/facilities
avg_dis_min=1.0
potential_facilities=[]
NearFacilityList=[]
nearCustomer=[]
nearCustomers=[]
geo_instance=1
pmp_I_eaquls_J=1

#parameters for districting
location_problem=1
max_num_facility=999
max_facility_cost=-1
max_facility_travel_cost=-1
max_num_reserved_facility=0
adaptive_number_of_facilities=1
fixed_cost_obj=1
travel_distance_weight=1
spatial_contiguity=0 # 0 no, 1 yes, 2 yes with multi-parts
spatial_contiguity_minimum_percentage=5
pop_dis_coeff=10000.0 #used in the objective function
penalty_on_demand=10000
pop_deviation=0.00 #for pdp, 5%
cflp_max_service_radius=10000.0
cflp_service_radius_preference=10000.0
cflp_min_service_coverage_percentage=100.0
envy_service_distance=10000.0
#travel_distance_weight=1 #pmp only
envy_objective_weight=0
envy_service_objective=0 
mean_distance_epsilon=0.01    #ϵ-constrained method
#0: no envy; 
#1: envy obj with weight; 
#2: envy constraint with CV; 
#3: envy with 0 weight on sum_dis, MELP
#4: envy(abs_dev) obj with weight; 
envy_coefficient_variation=0.5

#current solution
centersID=[]
node_groups=[]
district_info=[] #[[0,0,0.0] for x in range(num_districts)] # solution
objective_overload=0
obj_balance=MAXNUMBER
objective=MAXNUMBER
objective_fcost=0.0
biobjective=MAXNUMBER
objective_supply=0.0
objective_envy=0.0
objective_covered=0
objective_rmax_not_covered=0
objective_pentalty_on_overload=0.0
objective_pentalty_on_rmax=0.0
objective_pentalty_on_covering=0.0

given_solution=0 #reserved
all_solutions=[]

#best solution in each start
best_solution =[] # node_groups[:]
best_centersID=[]
best_biobjective=MAXNUMBER
best_objective=MAXNUMBER
best_objective_overload = MAXNUMBER
best_objective_fcost = 0.0
#global best solution 
#best_centers_global=[]
best_solution_global=[]
best_centersID_global=[]
best_biobjective_global = MAXNUMBER
best_objective_global = MAXNUMBER
best_objective_fcost_global = 0.0
best_overload_global = MAXNUMBER

#search statistics
time_check=0
time_check_edge_unit=0
time_spp=0.0
time_update_centers=0.0
time_op=[0.0 for x in range(10)]
time_ruin_recreate=[0.0 for x in range(10)]
time_location=[0.0 for x in range(10)]
time_pmp_re_location=0.0
time_Whitaker=0.0
time_LNS1=0.0
time_LNS2=0.0
time_repair=0
count_op=[0.0 for x in range(10)]
check_count=0
improved=0
move_count=0

#search histry
region_pool = []
pool_index=[]

#local search
acceptanceRule="hc" #solver name
assignment_operators_selected=[0,1] #0 one-unit move, 1 two-unit move, 2 three-unit move
location_operators_selected=[0,1,2,3,4] #0 swap, 1 drop, 2 add, 3 add+drop, 4 me
ruin_oprators=[0,1,2,3,4] #ruin0, ruin1, 9 mip assign
sub_model_neigborhood_types=[0]
multi_start_count=6 #population size for GA, ILS, VNS, LIS+VND
initial_solution_method=0 #0 construction, 1 LP
assign_method=0 #not used
assign_or_Location_search_method=0
large_facility_cost=0
maxloops=1000
max_loops_solution_not_improved=-1
SA_maxloops = 100 # maximum number of search loops for GA
SA_temperature=1.0
op_random = 1 # operators used sequentially (0) or randomly(1)
last_loop_obj=0.0
ruin_percentage=20
mainloop=0
mutation_rate=0.01 
cross_methods=-1
adj_pop_loops=5000
solution_similarity_limit=10.0

#mip modelling for inititail solution, spp and full model
is_spp_modeling=0 #0 no spp modelling, 1 modelling at the end, 2 modelling in case of local optimum
linear_relaxation=0
spp_loops=400
solver_time_limit=7200 #used for mip modeling
solver_mipgap=0.000000000001
solver_message=0
heuristic_time_limit=300
seed =random.randint(0,10000)
random.seed(seed)
locTabuLength=100  #nf*psize
locTabuList=[]
locTabuList2=[]

def arcpy_print(s):
	if has_arcpy==1: 
		arcpy.AddMessage(s)
	else:
		print s

#record a region in current solution
def update_region_pool(rid):
	global pool_index
	global time_spp
	global region_pool
	t=time.time()
	if is_spp_modeling<=0: return
	if facilityMaximumCapacity>0 and  district_info[rid][1]>facilityMaximumCapacity: return
	if facilityMinimumCapacity>0 and  district_info[rid][1]<facilityMinimumCapacity: return
	if centersID[rid]<0: return
	#if spatial_contiguity==1 and check_continuality_feasibility(node_groups,rid)<1:
	#	 return
	ulist=[x for x in  range(num_units) if node_groups[x]==rid]
	if ulist==[]:
		#print "empty area:",rid,node_groups
		return
	cost1=district_info[rid][2]
	cost2=sum(nodedik[x][rid] for x in ulist)
	if location_problem==9: cost2=sum(nodedij[x][rid] for x in ulist)
	if abs(cost1-cost2)>0.001: print rid,cost1,cost2
	obj=district_info[rid][2]+district_info[rid][4]*pop_dis_coeff
	idx=int(obj*1000000)
	idx+=sum((x+13)*(x+137) for x in ulist)
	if idx not in pool_index[rid]:
		pool_index[rid].append(idx)
		region_pool.append([ulist,district_info[rid][2],district_info[rid][1],district_info[rid][4],rid])
	time_spp+=time.time()-t
	return

#record all regions in current solution
def update_region_pool_all():
	if is_spp_modeling<=0:
		return
	for rid in range (num_districts):
		if centersID[rid]<0: continue
		update_region_pool(rid)

#update region information of the current solution
def update_district_info():
	global objective_overload
	global objective
	global biobjective
	global objective_fcost
	global district_info
	global move_count
	global obj_balance
	global centersID
	global objective_supply
	global avg_dis_min
	for k in range(num_districts):
		district_info[k][0] = 0
		district_info[k][1] = 0.0
		district_info[k][2] = 0.0
		district_info[k][3] = 0.0
		district_info[k][4] = 0.0
	for k in range(num_districts):
		if centersID[k]<0 and k in node_groups:
			arcpy_print("debug: a facility not selected but used: " + str(k))
			#centersID[k]=facilityCandidate[k]
	for k in range(num_districts):
		if centersID[k]<0:
			continue
		ulist=[x for x in range(num_units) if node_groups[x]==k]
		if len(ulist)==0:
			if location_problem==3: continue
			'''if adaptive_number_of_facilities==1 and k not in facility_inclusion_list:
				centersID[k]=-1
				continue'''
		district_info[k][0] = len(ulist)
		district_info[k][1] = sum(nodes[x][3] for x in ulist)
		district_info[k][2] = sum(nodedik[x][k] for x in ulist)
		if location_problem==9: district_info[k][2] = sum(nodedij[x][k] for x in ulist)
		district_info[k][3] = facilityCapacity[k] 
		district_info[k][4] = max(0.0,district_info[k][1]-facilityCapacity[k]) # -district_info[k][3]
		if location_problem==3: district_info[k][4]=0 #pmp
		if location_problem==2: #pdp,edp
			bal=0.0
			dev=pop_deviation*total_pop/max_num_facility
			if district_info[k][1]>district_info[k][3]+dev: bal=district_info[k][1]-district_info[k][3]-dev
			if district_info[k][1]<district_info[k][3]-dev: bal=district_info[k][3]-district_info[k][1]-dev
			district_info[k][4]=bal
		#print centersID,node_groups
	bal=sum(x[4] for x in district_info)
	objective=sum([x[2] for x in district_info])
	objective_overload=bal
	#if objective/total_pop<avg_dis_min:
	#	 avg_dis_min=objective/total_pop
	avg_dis_min=objective/total_pop
	biobjective=objective+objective_overload*avg_dis_min*pop_dis_coeff

	objective_supply=sum(facilityCapacity[x] for x in range(num_districts) if centersID[x] >=0)
	#biobjective=objective+objective_overload*avg_dis_min*1000000
	#biobjective=bal2*avg_dis_min*1000000
	fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x] >=0)
	objective_fcost=fcost
	if fixed_cost_obj==1:
		biobjective+=fcost
	move_count+=1


def update_best_solution():
	global best_solution
	global best_centersID
	global best_biobjective
	global best_objective
	global best_objective_fcost
	global best_overload
	global best_objective_overload
	global best_centersID_global
	global best_solution_global
	global best_biobjective_global
	global best_objective_global
	global best_objective_fcost_global
	global best_overload_global	   
	global improved_loop
	global improved
	global avg_dis_min
	improve =0
	if location_problem==1 and adaptive_number_of_facilities==0:
		nf=sum(1 for x in centersID if x>=0)
		if nf!=max_num_facility: return 0
	#if spatial_contiguity==1 and check_solution_continuality_feasibility(node_groups)==0:
	#	 ##noprint "check_solution_continuality_feasibility!!!"
	#	 return improve
	biobj=biobjective
	biobj_best=best_biobjective
	if biobj<=biobj_best:
		best_biobjective=biobj
		best_objective = objective
		best_objective_fcost=objective_fcost
		best_objective_overload = objective_overload
		best_solution = node_groups[:]
		best_centersID=centersID[:]
		improved_loop=mainloop
		improve =1
		improved+=1
	if biobj<best_biobjective_global:
		best_biobjective_global=biobj
		best_centersID_global=centersID[:]
		best_overload_global = objective_overload
		best_solution_global =node_groups[:]
		best_objective_global = objective
		best_objective_fcost_global=objective_fcost
		avg_dis_min=biobj/total_pop
	return improve


def read_pmp_instance(pfile):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global geo_instance
	geo_instance=0
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	if len(items)==1:
		items = line.split('\t')
	num_units=int(items[0])
	num_districts=int(items[0])
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	for i in range(num_districts):
		line = f.readline()
		line=line[0:-1]
		items = line.split('\t')
		for j in range(num_units):
			nodedik[j][i]=int(items[j])
			nodedij[j][i]=int(items[j])
	#for i in range(num_districts): print nodedik[i]
	line = f.readline()
	line = f.readline()
	line=line[0:-1]
	items = line.split('\t')
	for i in range(num_units):
		facilityCost[i]=int(items[i])
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0

	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	#print "NearFacilityList:"
	#for i in range(num_districts): print NearFacilityList[i]
	find_near_customer()

	for i in range(num_units):
		node_neighbors.append(NearFacilityList[i][:8])

	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_pmp_or_instance(pfile): #read pmed instances
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global max_num_facility
	global district_info
	global avg_dis_min
	global potential_facilities
	global geo_instance
	geo_instance=0
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line=line.strip()
	#line=line[0:-1]
	items = line.split(' ')
	num_units=int(items[0])
	num_districts=int(items[0])
	num_links=int(items[1])
	max_num_facility =int(items[2])	  
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N:P "+str(num_districts)+" "+str(num_units) +" "+ str(max_num_facility)) 
	node_neighbors=[ [] for x in range(num_units)]
	links={}
	for i in range(num_links):
		line = f.readline()
		line = line.strip()
		#line=line[0:-1]
		items = line.split(' ')
		n1=int(items[0])-1
		n2=int(items[1])-1
		#print line,items
		links[str(n1)+"_"+str(n2)]=int(items[2])
		links[str(n2)+"_"+str(n1)]=int(items[2])
		node_neighbors[n1].append(n2)
		node_neighbors[n2].append(n1)
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	#for i in range(num_units):
	#	  print i, node_neighbors[i]

	#nodedij
	for i in range(num_units):
		dist=[int(MAXNUMBER) for x in range(num_units)]
		dist[i]=0
		inlist=[i]
		while 1:
			if inlist==[]: break
			u=inlist[0]
			del inlist[0]
			for x in node_neighbors[u]:
				if dist[u]+links[str(u)+"_"+str(x)]<dist[x]:
					dist[x]=dist[u]+links[str(u)+"_"+str(x)]
					if x not in inlist: 
						inlist.append(x)
		nodedij[i]=dist[:]
		nodedik[i]=dist[:]
	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	find_near_customer()
	
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_pmp_pm_instance(pfile): #cost???
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global geo_instance
	geo_instance=0
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line = f.readline() #I,J
	line = f.readline() #I,J
	line=line.strip()
	#line=line[0:-1]
	items = line.split(' ')
	num_units=int(items[0])
	num_districts=int(items[0])
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [1000 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [1000 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	node_neighbors=[ [] for x in range(num_units)]
	links={}
	line = f.readline() #I,J
	line = f.readline() #I,J
	while 1:
		line = line.strip()
		if len(line)<2: break
		items = line.split(' ')
		n=len(items)
		for i in range(1,n+1):
			if items[n-i]=="": del items[n-i]
		n1=int(items[0])-1
		n2=int(items[1])-1
		#links[str(n1)+"_"+str(n2)]=int(items[2])
		nodedij[n2][n1]=int(items[2])
		nodedik[n2][n1]=int(items[2])
		#node_neighbors[n1].append(n2)
		#node_neighbors[n2].append(n1)
		line = f.readline()
	f.close()
	#print node_neighbors
	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	#for i in range(num_units):
	#	  print i, node_neighbors[i]

	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	find_near_customer()
	
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)
def read_pmp_rw_instance(pfile):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global geo_instance
	geo_instance=0
	node =[0,0,0,1,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(pfile)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	num_units=int(items[1])
	num_districts=int(items[2])
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[num_units for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	line = f.readline() #I,J
	for idx in range(num_units*num_districts):
		line = f.readline()
		line=line[0:-1]
		items = line.split(' ')
		i=int(items[1])-1
		j=int(items[2])-1
		c=int(items[3])
		nodedik[i][j]=c
		nodedij[i][j]=c
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0

	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	#print "NearFacilityList:"
	#for i in range(num_districts): print NearFacilityList[i]
	find_near_customer()

	#for i in range(num_units):
	#	 node_neighbors.append(NearFacilityList[i][:8])
	create_node_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)
def read_bm_instance(f1): #read instances from or-lib(beasily),holmberge,yang...
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global geo_instance
	geo_instance=0
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(f1)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	idx=0
	for item in items:
		if item=="":
			continue
		if idx==0:
			num_districts=int(item)
			idx+=1
		else:
			num_units=int(item)
			idx+=1
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[0.0 for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))
	for i in range(num_districts):
		line = f.readline()
		line=line[0:-1]
		items = line.split(' ')
		idx=0
		for item in items:
			if item=="":
				continue
			if idx==0:
				facilityCapacity[i]=float(item)
				idx+=1
			else:
				facilityCost[i]=float(item)
				idx+=1
	idx=0
	line = f.readline()
	while line: # for i in range((num_units+1)/10):
		line=line[0:-1]
		items = line.split(' ')
		for item in items:
			if item=="":
				continue
			if idx<num_units:
				nodes[idx][3]=float(item)
				idx+=1
			else:
				#i=(idx-num_units)/num_districts
				#k=(idx-num_units)%num_districts
				i=(idx-num_units)%num_units
				k=(idx-num_units)/num_units
				nodedik[i][k]=float(item)
				nodedij[i][k]=float(item)/nodes[i][3]
				idx+=1
		line = f.readline()	   
	f.close()

	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	#print NearFacilityList
	find_near_customer()
	create_node_neighbors()
	#find_nearFacilityFacility()
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def read_bm_instance2(f1):#read tbed instances
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global geo_instance
	geo_instance=0
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	f = open(f1)
	line = f.readline() #I,J
	line=line[0:-1]
	items = line.split(' ')
	if line.find("\t"): items = line.split('\t')
	idx=0
	for item in items:
		if item=="":
			continue
		if idx==0:
			num_units=int(item)
			idx+=1
		else:
			num_districts=int(item)
			idx+=1
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[0.0 for x in range(num_districts)]
	facilityCost=[0.0 for x in range(num_districts)]
	nodes=[node[:] for x in range(num_units) ]
	nodedik=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	nodedij=[ [0.0 for x in range(num_districts)] for x in range(num_units) ]
	arcpy_print("M,N: "+str(num_districts)+" "+str(num_units))

	idx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			nodes[idx][3]=float(item)
			idx+=1
		if idx==num_units: break

	fidx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			facilityCapacity[fidx]=float(item)
			fidx+=1
		if fidx==num_districts: break
	fidx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			facilityCost[fidx]=float(item)
			fidx+=1
		if fidx==num_districts: break
	idx=0
	while 1:
		line = f.readline()
		line=line[0:-1]
		if line=="": continue
		items = line.split(' ')
		if line.find("\t")>=0: items = line.split('\t')
		for item in items:
			if item=="":
				continue
			k=idx/num_units
			i=idx%num_units
			idx+=1
			nodedik[i][k]=float(item)*nodes[i][3]
			nodedij[i][k]=float(item)
		if idx==num_units*num_districts: break
	f.close()
	centersID=facilityCandidate[:]
	total_pop=sum(x[3] for x in nodes)
	total_supply=sum(facilityCapacity)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	avg_dis_min=1.0
	create_facility_neighbors()
	find_NearFacilityList(num_districts)
	find_near_customer()
	#find_nearFacilityFacility()
	create_node_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="total demand: "+ str(total_pop)
	arcpy_print(s)
	s="total supply: "+str(total_supply)
	arcpy_print(s)

def create_facility_neighbors():
	return 
	global facility_neighbors
	mindij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_districts)]
	for i in range(num_districts):
		for j in range(num_districts):
			if j<=i: continue
			dlist=[nodedij[x][i]-nodedij[x][j] for x in range(num_units)]
			d=sum(x*x for x in dlist)
			mindij[i][j]=d
			mindij[j][i]=d
	facility_neighbors = [[]for x in range(num_districts)]
	for i in range(num_districts):
		dlist=[[x, mindij[i][x]] for x in range(num_districts) ]
		dlist.sort(key=lambda x:x[1])
		nghrs=[x[0] for x in dlist]
		facility_neighbors[i]=nghrs[:]

def create_node_neighbors():
	global node_neighbors
	#rlist=[x for x in range(num_districts)]
	mindij=[[MAXNUMBER for x in range(num_units)] for y in range(num_units)]
	for i in range(num_units):
		for j in range(num_units):
			if j<=i: continue
			dlist=[nodedij[i][x]-nodedij[j][x] for x in range(num_districts)]
			d=sum(x*x for x in dlist)
			mindij[i][j]=d
			mindij[j][i]=d
	node_neighbors = [[]for x in range(num_units)]
	for i in range(num_units):
		dlist=[[x, mindij[i][x]] for x in range(num_units) ]
		dlist.sort(key=lambda x:x[1])
		nn=8
		if nn>num_units: nn=num_units
		nghrs=[dlist[x][0] for x in range(nn)]
		random.shuffle(nghrs) #debug
		node_neighbors[i]=nghrs[:]

#read instance file, f1:unit info, f2: connectivity info
def readfile(f1,f2):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	global facility_inclusion_list
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	#nodes.append(node)
	print "reading nodes ...",
	f = open(f1)
	line = f.readline()	 #OID	 pop	PointX	  PointY	fcadidature	   fcost	fcapacity
	line = f.readline()
	nodeidx=0
	while line:
		line=line[0:-1]
		#print line
		items = line.split(',')
		if len(items)<=2:
			items = line.split()
		unit=[nodeidx, float(items[2]), float(items[3]), int(items[1]),int(items[0]),int(items[6]),int(items[4]),float(items[5])]
		nodes.append(unit)
		nodeidx+=1
		#nodes.append([int(items[1]), float(items[8]), float(items[9]), int(items[5]), int(items[6]), int(items[7]),int(items[12]),int(items[13])])
		line = f.readline()
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	##noprint num_units,"units"
	##noprint "reading connectivity ...",
	###id1,id2#####
	node_neighbors = [[]for x in range(len(nodes))]
	if f2!="na":
		#connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]
		f = open(f2)
		line = f.readline()
		line = f.readline()
		links=0
		while line:
			items = line.split(',')
			if len(items)<=2:
				items = line.split()
			if int (items[1]) != int (items[2]):
				id1=int (items[1])
				id2=int (items[2])
				idx1=-1
				idx2=-1
				for i in range(num_units):
					if nodes[i][4]==id1:
						idx1=i
					if nodes[i][4]==id2:
						idx2=i
					if idx1>=0 and idx2>0:
						break
				node_neighbors[idx1].append(idx2)
				node_neighbors[idx2].append(idx1)
				#connectivity[idx1][idx2]=1
				#connectivity[idx2][idx1]=1
				links+=1
			line = f.readline()
		f.close()
	##noprint links,"links"
	num_units=len(nodes)
	facilityCandidate=[]
	facilityCapacity=[]
	facilityCost=[]
	centersID=[]
	print "all data are read! "
	for i in range(num_units):
		if nodes[i][5]>0 or all_units_as_candadate_locations==1:
			facilityCandidate.append(i)
			facilityCapacity.append(nodes[i][5])
			facilityCost.append(nodes[i][7])
			centersID.append(i)
	num_facilityCandidate=len(facilityCandidate)
	num_districts=len(facilityCandidate)
	#facilityCandidate.sort()
	total_supply=sum(facilityCapacity)
	centersID=facilityCandidate[:]
	facility_inclusion_list=[]
	for k in range(num_districts):
		u=facilityCandidate[k]
		if nodes[u][6]==1:
			facility_inclusion_list.append(k)
	print "existing facilities", facility_inclusion_list
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	max_dij=0.0
	print "craeating distance matrix......"
	for i in range(num_units):
		for k in range(num_districts):
			j=facilityCandidate[k]
			d=0.0
			if distance_type==0:
				d2=pow(nodes[i][1]-nodes[j][1],2)
				d2+=pow(nodes[i][2]-nodes[j][2],2)
				d=pow(d2,0.5)/1000
			if distance_type==1:
				d=abs(nodes[i][1]-nodes[j][1])
				d+=abs(nodes[i][2]-nodes[j][2])
				d/=1000
			if distance_type==2: #geo
				d=abs(nodes[i][1]-nodes[j][1])
				d+=abs(nodes[i][2]-nodes[j][2])
				d/=1000
			nodedij[i][k]=d
			if d>max_dij:
				max_dij=d
	''' 
	if len(node_neighbors)>0:
		for i in range(len(nodes)):
			for j in range(len(nodes)):
				if j<=i:
					continue
				if connectivity[i][j]==1:
					node_neighbors[i].append(j)
					node_neighbors[j].append(i)'''

	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	dis=0.0
	for i in range(num_units):
		d=min(nodedij[i])
		dis+=d*nodes[i][3]
	avg_dis_min=dis/total_pop
	#weighted cost from i to k
	
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="M N: "+str(num_districts)+" "+str(num_units)
	arcpy_print(s)
	s="Total demand & supply: "+str(total_pop)+" "+str(total_supply)+" "+str(sum(facilityCost))
	arcpy_print(s)


def readfile_ab(f1,f2,f3):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global district_info
	global avg_dis_min
	global potential_facilities
	node =[0,0,0,0,0,0,0,0,0,0]
	#school_nodes = []
	nodes = []
	#nodes.append(node)
	##noprint "reading nodes ...",
	f = open(f1)
	line = f.readline()	 #OID	PointX	  PointY    demand  sub_region    
	line = f.readline()
	nodeidx=0
	while line:
		line=line[0:-1]
		items = line.split(',')
		if len(items)<=2:
			items = line.split('\t')
		unit=[int(items[0]), float(items[1]), float(items[2]), int(items[3]),0,int(items[4])]
		nodes.append(unit)
		nodeidx+=1
		line = f.readline()
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	f = open(f2)
	line = f.readline()	 #OID	PointX	  PointY    cap fcost   existing facility
    
	line = f.readline()
	nodeidx=0
	while line:
		line=line[0:-1]
		items = line.split(',')
		if len(items)<=2:
			items = line.split('\t')
		unit=[int(items[0]), float(items[1]), float(items[2]), int(items[3]),int(items[4]),int(items[5])]
		nodes.append(unit)
		if unit[5]==1: facility_inclusion_list.append(nodeidx)
		nodeidx+=1
		line = f.readline()
	f.close()
	print "facility_inclusion_list:", facility_inclusion_list
			    
	num_districts=len(nodes)-num_units
	
	facilityCandidate=[num_units+x for x in range(num_districts)]
	facilityCapacity=[nodes[num_units+x][3] for x in range(num_districts)]
	facilityCost=[nodes[num_units+x][4] for x in range(num_districts)]
	centersID=facilityCandidate[:]
	num_facilityCandidate=len(facilityCandidate)

	total_supply=sum(facilityCapacity)
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	if f3=="":
		for i in range(num_units):
			for k in range(num_districts):
				j=num_units+k
				d=0.0
				if distance_type==0:
					d2=pow(nodes[i][1]-nodes[j][1],2)
					d2+=pow(nodes[i][2]-nodes[j][2],2)
					d=pow(d2,0.5)/1000
				if distance_type==1:
					d=abs(nodes[i][1]-nodes[j][1])
					d+=abs(nodes[i][2]-nodes[j][2])
					d/=1000
				if distance_type==2: #geo
					d=abs(nodes[i][1]-nodes[j][1])
					d+=abs(nodes[i][2]-nodes[j][2])
					d/=1000
				nodedij[i][k]=d
	else:
		f = open(f3)
		line = f.readline()
		readsuccess=1
		for i in range(num_units):
			line = f.readline()
			items = line.split()
            #len(items)
			for k in range(num_districts):
				d=float(items[k+1])
				nodedij[i][k]=d/1000
		f.close()
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	create_node_neighbors()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]
	s="M N: "+str(num_districts)+" "+str(num_units)
	arcpy_print(s)
	s="Demand and supply: "+str(total_pop)+" "+str(sum(facilityCapacity))
	arcpy_print(s)    



def read_cpmp_file(f1):
	global num_units
	global total_pop
	global total_supply
	global nodes
	global node_neighbors
	global nodedij
	global nodedik
	global centersID
	global facilityCandidate
	global facilityCapacity
	global facilityCost
	global num_facilityCandidate
	global num_districts
	global avg_dis_min
	global max_num_facility
	global district_info
	node =[0,0,0,0,0,0,0,0,0,0]
	nodes = []
	##noprint "reading nodes ...",
	f = open(f1)
	line = f.readline()	 #OID	 pop	PointX	  PointY	fcadidature	   fcost	fcapacity
	line=line[0:-1]
	line=line.strip()
	items = line.split()
	items = line.split()
	n=int(items[0])
	p=int(items[1])
	max_num_facility=p	  
	for nodeidx in range(n):
		line = f.readline()
		line=line[0:-1]
		line=line.strip()
		items = line.split()
		unit=[nodeidx, float(items[0]), float(items[1]), int(items[3]),nodeidx,int(items[2]),0,0]
		if len(items)>=5: unit[6]=float(items[4])
		nodes.append(unit)
	f.close()
	num_units=len(nodes)
	total_pop=sum(x[3] for x in nodes)
	connectivity=[[0 for x in range(len(nodes))] for y in range(len(nodes))]
	num_districts=num_units
	##noprint links,"links"
	num_units=len(nodes)
	facilityCandidate=[x for x in range(num_districts)]
	facilityCapacity=[nodes[x][5] for x in range(num_districts)]
	facilityCost=[nodes[x][6] for x in range(num_districts)]
	centersID=[x for x in range(num_districts)]

	total_supply=sum(facilityCapacity)
	nodedij=[[MAXNUMBER for x in range(num_districts)] for y in range(num_units)]
	max_dij=0.0
	for i in range(num_units):
		for j in range(num_districts):
			d2=pow(nodes[i][1]-nodes[j][1],2)
			d2+=pow(nodes[i][2]-nodes[j][2],2)
			d=pow(d2,0.5)
			nodedij[i][j]=d
			if d>max_dij:
				max_dij=d
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	nodedik=[[nodedij[y][x]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	find_NearFacilityList(num_districts)
	print "find_near_customer()..."
	find_near_customer()
	#find_nearFacilityFacility()
	print "create_facility_neighbors()..."
	create_facility_neighbors()
	potential_facilities=[x for x in range(num_districts)]

	node_neighbors = [[]for x in range(len(nodes))]
	s="M N: "+str(num_districts)+" "+str(num_units)
	s+="\nTotal demand: "+str(total_pop)
	s+="\nTotal supply: "+str(total_supply)
	s+="\nTotal cost: "+str(sum(facilityCost))
	arcpy_print(s)
	#s="Total demand & supply: "+str(total_pop)+" "+str(total_supply)
	arcpy_print(s)

def find_nearFacilityFacility():
	global nearFacilityFacility
	nearFacilityFacility=[[] for x in range(num_districts)]
	dkk=[sum(nodedik[x][k]*nodedik[x][k] for x in range(num_units)) for k in range(num_districts)]
	#dkk.sort(key=lambda x:x[1])
	#dlist=[x[0] for x in dkk]
	for k in range(num_districts):
		d=dkk[k]
		dk=[[x,dkk[x]-d] for x in range(num_districts)]
		dk.sort(key=lambda x:x[1])
		del dk[0]
		nearFacilityFacility[k]=[x[0] for x in dk]
	
def find_near_customer():
	global nearCustomer
	global nearCustomers
	if location_problem>=2 and pmp_I_eaquls_J==1: 
		nearCustomers=NearFacilityList
		nearCustomer=[x for x in range(num_districts)]
		return
	nearCustomer=[-1 for x in range(num_districts)]
	nearCustomers=[[] for x in range(num_districts)]
	dis=[]
	for k in range(num_districts):
		dis=[ [x,nodedij[x][k]] for x in range(num_units)]
		dis.sort(key=lambda x: x[1])
		nearCustomer[k]=dis[0][0]
		nearCustomers[k]=[x[0] for x in dis]
	   
def initialize_instance():
	global num_units
	global num_districts
	global num_facilityCandidate
	global centersID
	global node_groups
	global facilityCost
	global facilityCandidate
	global facilityCapacity
	global nodedik
	global avg_pop
	global total_pop
	global avg_dis_min
	global total_supply
	global fixed_cost_obj
	global max_num_facility
	global adaptive_number_of_facilities
	#solution obj 
	global district_info
	global objective_overload
	global objective
	global biobjective
	global all_solutions
	#best solution 
	global best_solution
	global best_centersID
	global best_biobjective
	global best_objective
	global best_objective_overload
	#global best solution 
	global best_solution_global
	global best_centersID_global
	global best_biobjective_global
	global best_objective_global
	global best_overload_global
	global potential_facilities
	global max_exclusion_list
	num_districts=len(facilityCandidate)
	#num_units=len(nodes)
	total_pop=sum(nodes[x][3] for x in range(num_units))
	#print total_pop,nodes[:10]
	#sum(nodes[x][3] for x in range(num_units))
	node_groups=[-1 for x in range(num_units)]
	if location_problem==0:
		fixed_cost_obj=0
		max_num_facility=num_districts
	'''if fixed_cost_obj==0:
		facilityCost=[0 for x in range(num_districts)]'''
	if location_problem==1 and max_num_facility<1:
		#max_num_facility=num_districts
		adaptive_number_of_facilities=1
	if location_problem==2:
		if all_units_as_candadate_locations==1:
			facilityCandidate=[x for x in range(num_districts)]
			facilityCost=[0.0 for x in range(num_districts)]
			popa=total_pop*1.0/max_num_facility
			facilityCapacity=[popa for x in range(num_districts)]
		if all_units_as_candadate_locations==0:
			facilityCost=[0.0 for x in range(num_districts)]
			popa=total_pop*1.0/max_num_facility
			facilityCapacity=[popa for x in range(num_districts)]
	if location_problem==3: #pmp
		#num_districts=num_units
		#facilityCandidate=[x for x in range(num_districts)]
		facilityCost=[0.0 for x in range(num_districts)]
		facilityCapacity=[total_pop for x in range(num_districts)]
	centersID=facilityCandidate[:]
	num_facilityCandidate=len(facilityCandidate)
	district_info = [[0,0.0,0.0,0.0,0.0] for x in range(num_districts)]
	total_supply=sum(facilityCapacity)
	#arcpy_print("total demand: "+str(total_pop))
	#arcpy_print("total supply: "+str(total_supply))
	#arcpy_print("avg. distance to nearest facility: "+str(avg_dis_min))

	objective_overload=MAXNUMBER
	obj_balance=MAXNUMBER
	objective=MAXNUMBER
	biobjective=MAXNUMBER
	all_solutions=[]

	#best solution in each start
	best_solution =[] # node_groups[:]
	best_centersID=[]
	best_biobjective=MAXNUMBER
	best_objective=MAXNUMBER
	best_objective_overload = MAXNUMBER

	#global best solution 
	best_solution_global=[]
	best_centersID_global=[]
	best_biobjective_global = MAXNUMBER
	best_objective_global = MAXNUMBER
	best_overload_global = MAXNUMBER
	#if geo_instance==1:
	#	 nodedik=[[nodedij[y][facilityCandidate[x]]*nodes[y][3] for x in range(num_districts)] for y in range(num_units)]
	avg_dis_min =sum(nodedik[x][0] for x in range(num_units))/total_pop
	if spatial_contiguity>=1:
		find_near_customer()
	find_NearFacilityList(num_districts)
	if linear_relaxation==1:
		lplocs,sol=location_model_linear_relexation(max_num_facility,0,heuristic_time_limit,0.0001) 
		potential_facilities=[x for x in range(num_districts) if lplocs[x]>0.0001]
		print "Potential facilities by Linear Relax",potential_facilities	 
	max_exclusion_list=[0.0 for x in range(num_districts)]


def find_NearFacilityList(nnn):
	global NearFacilityList
	if len(NearFacilityList)>0: return
	NearFacilityList=[]
	n=nnn#num_districts
	if n>num_districts: n=num_districts
	dis=0.0
	print "find_NearFacilityList()",
	for i in range(num_units):
		if i%100==0: print ".",
		fdlist=[ [x,nodedij[i][x]] for x in range(num_districts)]
		fdlist.sort(key=lambda x:x[1])
		flist=[x[0] for x in fdlist[0:n]]
		NearFacilityList.append(flist[:])
	print "data samples"
	for i in range(10):
		u=(i*17)%num_units
		print u,NearFacilityList[u][:10]
	if geo_instance==0:
		return
			

def me_uflp_model(time_limit,mipgap): 
	global centersID
	global node_groups
	global all_solutions
	prob = pulp.LpProblem("me_uflp",pulp.LpMinimize)
	centers=range(num_districts)#facilityCandidate
	xvariables={}
	costs={}
	ulist=range(num_units)
	for i in ulist:
		for j in centers:
			xvariables["x_" +str(i)+ "_"+ str(j)]=pulp.LpVariable("x_" +str(i)+ "_"+ str(j), 0, 1, pulp.LpContinuous) #pulp.LpBinary
			costs["x_" +str(i)+ "_"+ str(j)]= nodedik[i][j]*travel_distance_weight
			d=nodedij[i][j]
			if envy_service_objective==1 and d>envy_service_distance:
				costs["x_" +str(i)+ "_"+ str(j)]+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
	yvariables={}
	for i in centers:
		yvariables["y_" +str(i)]=pulp.LpVariable("y_" +str(i), 0, 1, pulp.LpBinary)
		costs["y_" +str(i)]=facilityCost[i]

	obj=""
	if fixed_cost_obj==1:
		for x in yvariables:
			obj +=costs[x]* yvariables[x]
	for x in xvariables:
		obj +=costs[x]* xvariables[x]
	prob += obj

	#cons 2
	for i in ulist:
		s=""
		for j in centers:
			s+=xvariables["x_" +str(i)+ "_"+ str(j)]
		prob += s==1

	for k in centers:
		s=""
		for i in ulist:
			s+= xvariables["x_" +str(i) + "_"+ str(k) ]
		s-= num_units*yvariables["y_" +str(k)]
		prob += s <= 0

	if facilityMinimumCapacity>0:
		for k in centers:
			s=""
			for i in ulist:
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			prob += s >= facilityMinimumCapacity*yvariables["y_" +str(k)]
	if facilityMaximumCapacity>0:
		for k in centers:
			s=""
			for i in ulist:
				s+= nodes[i][3]*xvariables["x_" +str(i) + "_"+ str(k) ]
			prob += s <= facilityMaximumCapacity*yvariables["y_" +str(k)]

	'''for k in centers:
		s=""
		for i in ulist:
			s+= xvariables["x_" +str(i) + "_"+ str(k) ]       
		prob += s <= num_units*yvariables["y_" +str(k)]'''

	if max_facility_cost>0:
		s=""
		for k in centers:
			s+=facilityCost[k]*yvariables["y_" +str(k)]
		prob += s <= max_facility_cost
	
	'''for i in ulist:
		for k in centers:
			s=""
			for j in centers:
				s=nodedij[i][j]*xvariables["x_" +str(i)+"_"+str(j)]
				s += (bigM-nodedij[i][k])*yvariables["y_"+str(k)]
				prob +=s  <= bigM'''

	prob.writeLP("_ce_uflp.lp")
	gap=mipgap
	solver=""
	if mip_solver=='cbc':
		solver=pulp.apis.COIN_CMD(mip=1,msg=solver_message,gapRel = gap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex':
		solver=pulp.apis.cplex_api.CPLEX_CMD(mip=1,msg=solver_message, timeLimit=time_limit, options=['set mip tolerances mipgap '+ str(gap), 'set parallel -1'])
	if mip_solver=='gurobi':
		solver=pulp.apis.GUROBI_CMD(mip=1,msg=solver_message, timeLimit=time_limit,options=[("MIPGap",gap),("TimeLimit",time_limit)])
	solver.setTmpDir()
	solver.actualSolve(prob)

	if prob.status<=0:
		print "model unsolved... or infeasible"
		return []
	centersID=[-1 for x in range(num_districts)]
	if len(node_groups)<1: node_groups=[-1 for x in range(num_units)]
	for v in prob.variables():
		if (v.varValue >= 0.90):
			items=v.name.split('_')
			i=int(items[1])
			if items[0]=='y':
				centersID[i]=facilityCandidate[i]
			if items[0]=='x':
				node_groups[i]=int(items[2])
	#update_cflpr_district_info(1000000.0,10,0)
	update_envy_district_info()    
	return 1


def update_envy_district_info():
	global biobjective
	global objective_envy
	update_district_info()
	penalty=penalty_on_demand
	biobjective=objective*travel_distance_weight+objective_fcost*fixed_cost_obj
	if max_facility_cost>0:    
		fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		efcost=max(0,fcost-max_facility_cost)
		biobjective+=efcost*penalty
	if facilityMinimumCapacity>0:
		lowload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			lowload += max(0, facilityMinimumCapacity-district_info[k][1])
		biobjective+=penalty_on_demand*lowload
	if facilityMaximumCapacity>0:
		overload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			overload += max(0, district_info[k][1]-facilityMaximumCapacity)
		biobjective+=penalty_on_demand*overload
       
	if envy_service_objective==1:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
		objective_envy=envyobj
		biobjective += envyobj
	if envy_service_objective==4:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
		objective_envy=envyobj
		biobjective += envyobj
	if envy_service_objective==2:
		envyobj=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envyobj+=nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
		var=envy_coefficient_variation*envy_service_distance
		maxobj= 0.5* total_pop * var*var
		objective_envy=0.0
		if envyobj>maxobj: 
			objective_envy=penalty*(envyobj-maxobj)
		biobjective += objective_envy


def pmp_envy_find(fi,facility2): #find fr for fi
	savings=0.0
	loss=[[x,0.0] for x in range(num_districts)]
	if fixed_cost_obj==1: 
		savings-=facilityCost[fi]
		loss=[[x,-facilityCost[x]] for x in range(num_districts)]
	if max_facility_cost>0:
		fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for k in range(num_districts):       
			fcost_new = fcost-facilityCost[k]+facilityCost[fi]
			loss[k][1]-= max(0,fcost-max_facility_cost)*penalty_on_demand
			loss[k][1]+= max(0,fcost_new-max_facility_cost)*penalty_on_demand
	w=travel_distance_weight
	for i in range(num_units):
		k=node_groups[i]
		if nodedik[i][fi]<nodedik[i][k]: 
			savings+=nodedik[i][k]*w-nodedik[i][fi]*w
		else:
			loss[k][1]+=min(nodedik[i][fi],nodedik[i][facility2[i]])*w-nodedik[i][k]*w
		if envy_service_objective==1:
			envy1=0.0
			envy2=0.0
			envy3=0.0
			d=nodedij[i][k]
			if d>envy_service_distance:
				envy1=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			d=nodedij[i][fi]
			if d>envy_service_distance:
				envy2=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			d=nodedij[i][facility2[i]]
			if d>envy_service_distance:
				envy3=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if nodedij[i][fi]<nodedij[i][k]:
				savings+=envy1-envy2
			else:
				loss[k][1]+=min(envy2,envy3)-envy1
		if envy_service_objective==4:
			envy1=0.0
			envy2=0.0
			envy3=0.0
			d=nodedij[i][k]
			if d>envy_service_distance:
				envy1=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			d=nodedij[i][fi]
			if d>envy_service_distance:
				envy2=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			d=nodedij[i][facility2[i]]
			if d>envy_service_distance:
				envy3=nodes[i][3]*envy_objective_weight*(d-envy_service_distance)
			if nodedij[i][fi]<nodedij[i][k]:
				savings+=envy1-envy2
			else:
				loss[k][1]+=min(envy2,envy3)-envy1
	loss=[x for x in loss if centersID[x[0]]>=0]
	if len(loss)<1: return -1,-1.0
	loss.sort(key=lambda x:x[1])
	if facilityMinimumCapacity<0: #debuging
		shortage=0
		for k in range(num_districts):
			if centersID[k]>=0:
				shortage += max(0, facilityMinimumCapacity -district_info[k][1])
		for idx in range(len(loss)):
			caplist=[district_info[x][1] for x in range(num_districts)]
			fr=loss[idx][0]
			caplist[fr]=0
			for i in range(num_units):
				k=node_groups[i]
				if k!=fr: 
					if nodedij[i][fi]<nodedij[i][k]: 
						caplist[fi]+=nodes[i][3]
						caplist[k]-=nodes[i][3]
					continue              
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					if k==fr: continue
					if k==fi:
						caplist[fi]+=nodes[i][3]
						break
					caplist[k]+=nodes[i][3]
					break
			shortage2=0
			for k in range(num_districts):
				if caplist[k]>0:
					shortage2 += max(0, facilityMinimumCapacity -caplist[k])
			#print [sum(caplist),shortage,shortage2],[x for x in caplist if x>0]
			if shortage2<=shortage:
				#print [sum(caplist),shortage,shortage2],
				break             
			loss[idx][1]+= (shortage2-shortage) * penalty_on_demand
		loss.sort(key=lambda x:x[1])
	fr=loss[0][0]
	profit=savings-loss[0][1]
	return fr,profit
	
def pmp_find(fi,facility2): #find fr for fi
	if envy_service_objective==1:
		return pmp_envy_find(fi,facility2)
	if envy_service_objective==4:
		return pmp_envy_find(fi,facility2)
	savings=0.0
	loss=[[x,0.0] for x in range(num_districts)]
	if fixed_cost_obj==1: 
		savings=-facilityCost[fi]
		loss=[[x,-facilityCost[x]] for x in range(num_districts)]
	if max_facility_cost>0:
		fcost=sum(facilityCost[x] for x in range(num_districts) if centersID[x]>=0)
		for k in range(num_districts):       
			fcost_new = fcost-facilityCost[k]+facilityCost[fi]
			loss[k][1]-= max(0,fcost-max_facility_cost)*penalty_on_demand
			loss[k][1]+= max(0,fcost_new-max_facility_cost)*penalty_on_demand
	for i in range(num_units):
		k=node_groups[i]
		if nodedik[i][fi]<nodedik[i][k]: 
			savings+=nodedik[i][k]-nodedik[i][fi]
		else:
			loss[k][1]+=min(nodedik[i][fi],nodedik[i][facility2[i]])-nodedik[i][k]
	loss=[x for x in loss if centersID[x[0]]>=0]
	loss.sort(key=lambda x:x[1])
	if facilityMinimumCapacity<0: #debuging
		shortage=0
		for k in range(num_districts):
			if centersID[k]>=0:
				shortage += max(0, facilityMinimumCapacity -district_info[k][1])
		for idx in range(len(loss)):
			caplist=[district_info[x][1] for x in range(num_districts)]
			fr=loss[idx][0]
			caplist[fr]=0
			for i in range(num_units):
				k=node_groups[i]
				if k!=fr: 
					if nodedij[i][fi]<nodedij[i][k]: 
						caplist[fi]+=nodes[i][3]
						caplist[k]-=nodes[i][3]
					continue              
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					if k==fr: continue
					if k==fi:
						caplist[fi]+=nodes[i][3]
						break
					caplist[k]+=nodes[i][3]
					break
			shortage2=0
			for k in range(num_districts):
				if caplist[k]>0:
					shortage2 += max(0, facilityMinimumCapacity -caplist[k])
			#print [sum(caplist),shortage,shortage2],[x for x in caplist if x>0]
			if shortage2<=shortage:
				#print [sum(caplist),shortage,shortage2],
				break             
			loss[idx][1]+= (shortage2-shortage) * penalty_on_demand
	loss.sort(key=lambda x:x[1])
	fr=loss[0][0]
	profit=savings-loss[0][1]
	return fr,profit

#On the implementation of a swap-based local search procedure for the p-median problem
def pmp_Whitaker():
	#return pmp_TB()
	global node_groups
	global centersID
	global time_Whitaker
	#global TB_tabu_list
	#if centersID in TB_tabu_list: return -1
	t=time.time()
	facility2=[0 for x in range(num_units)] #num_districts
	for i in range(num_units):
		k1=node_groups[i]
		for k2 in NearFacilityList[i]:
			if centersID[k2]>=0 and k2!=k1: 
				facility2[i]=k2
				break
	klist=[x for x in range(num_districts) if centersID[x]<0]
	random.shuffle(klist)
	improved=0
	best_swap=[-1,-1,0.0]
	swap=[]
	for nk in klist:
		k,profit=pmp_find(nk,facility2)
		if profit<=0: continue
		swap.append([k,nk,profit])
		if profit>best_swap[2]:
			best_swap[0]=k
			best_swap[1]=nk
			best_swap[2]=profit
		if len(swap)>=3:
			break
	swap.sort(key=lambda x:-x[2])
	if best_swap[0]>=0:
		#k=best_swap[0]
		#nk=best_swap[1]
		idx=0
		if len(swap)>2:
			idx=random.randint(0,1)
		#idx=0
		k=swap[idx][0]
		nk=swap[idx][1]
		centersID[k]=-1
		centersID[nk]=facilityCandidate[nk]
		for i in range(num_units):
			j=node_groups[i]
			if j!=k:
				if nodedik[i][j]>nodedik[i][nk]: node_groups[i]=nk
			else:
				for j in NearFacilityList[i]:
					if centersID[j]>=0:
						node_groups[i]=j
						break
		update_district_info()
		#print [x for x in centersID if x>=0]
		improved=1
	time_Whitaker+=time.time()-t
	if spatial_contiguity==1:
		repair_fragmented_solution()
	#if improved==-1: 
	#	 if centersID not in TB_tabu_list: TB_tabu_list.append(centersID[:])
	#print len(swap),
	return improved



def spp_mst():
	vars=[]		   
	num_pool=len(region_pool)
	for k in range(num_districts):
		ulist=[x for x in range(num_units) if node_groups[x]==k] 
		for i in range(num_pool):
			if ulist==region_pool[i][0] and region_pool[i][4]==k:
				vars.append([i,1])
				break
	return vars

def sppmodel(maxtime,mipgap):
	global node_groups
	global centersID
	if mip_solver not in mip_solvers:
		return 0
	if len(region_pool)<=10:
		##noprint "no candidate district!"
		print "len(region_pool)<=10", len(region_pool)
		return 0
	alpha_coeff=avg_dis_min*pop_dis_coeff  
	prob = pulp.LpProblem("_spp",pulp.LpMinimize)
	variables=[]
	costs=[]
	###noprint "buiding spp model..."
	#cost_stat=[]
	#cost_sum=[[0,0.0,0.0] for k in range(num_districts)]
	#for x in region_pool: print x
	for i in range(len(region_pool)):
		x=pulp.LpVariable("x_" +"{0:07d}".format(i), 0, 1,pulp.LpBinary)
		variables.append(x)
		cost=region_pool[i][1]*travel_distance_weight+region_pool[i][3]*alpha_coeff
		k=region_pool[i][4]
		#c2=sum(nodedik[x][k] for x in region_pool[i][0])
		#if abs(c2-cost)>0.001: print "check...", i,k,c2,cost,region_pool[i][1],region_pool[i][3]
		if fixed_cost_obj==1: ##[ulist,dis,demand,overload,k]
			cost+=facilityCost[k]
		if facilityMinimumCapacity>0:
			cost+=max(0,  facilityMinimumCapacity-region_pool[i][2]) *  alpha_coeff    
		if facilityMaximumCapacity>0:
			cost+=max(0,  region_pool[i][2] -facilityMaximumCapacity) *  alpha_coeff    
		if envy_service_objective==1:
			for j in region_pool[i][0]:
				if nodedij[j][k]>envy_service_distance:
					d=nodedij[j][k]-envy_service_distance
					cost+= nodes[j][3]* envy_objective_weight*d*d
		if envy_service_objective==4:
			for j in region_pool[i][0]:
				if nodedij[j][k]>envy_service_distance:
					d=nodedij[j][k]-envy_service_distance
					cost+= nodes[j][3]* envy_objective_weight*d
		costs.append(cost)
		#cost_stat.append(cost/region_pool[i][2])
		#cost_sum[k][0]+=1
		#cost_sum[k][1]+=cost/region_pool[i][2]
	#for k in range(num_districts):
	#	 if cost_sum[k][0]>0:
	#		 cost_sum[k][2]=cost_sum[k][1]/cost_sum[k][0]

	obj=""
	for i in range(len(region_pool)):
		obj+=costs[i]*variables[i]
	prob+=obj
	#for i in range(len(region_pool)):
	#	 k=region_pool[i][4]
	#	 if cost_stat[i]>cost_sum[k][2]:
	#		 prob+= variables[i]==0
	#print region_pool
	#print costs
	rlist=[[] for i in range(num_units)]
	for j in range(len(region_pool)):
		for x in region_pool[j][0]:
			rlist[x].append(j)
	for i in range(num_units):
		s=""
		for x in rlist[i]:
			s+=variables[x]
		if spatial_contiguity>0 or facilityMinimumCapacity>0:
			prob+=s == 1
		else:
			prob+=s >= 1
	if spatial_contiguity==0:
		for k in range(num_districts):
			s=""
			for i in range(len(region_pool)):
				if region_pool[i][4]!=k: continue
				s+=variables[i]
			if len(s)>0: prob+=s <= 1

	if adaptive_number_of_facilities==0:
		s=""
		for i in range(len(variables)):
			s+=variables[i]
		prob+= s==max_num_facility
	if max_facility_cost>0:
		s=""
		for i in range(len(region_pool)):
			k=region_pool[i][4]
			s+=facilityCost[k]*variables[i]
		prob+= s <= max_facility_cost
	prob.writeLP("_spp.lp")
	#mip_mst_file=tempfile.mkstemp()[1].split("\\")[-1]

	vars=spp_mst()
	for x,v in vars: variables[x].setInitialValue(v)
	solver=0
	if mip_solver=='cbc': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.COIN_CMD(timeLimit=maxtime,mip=1,msg=solver_message,gapRel=mipgap,options=['vnd on', 'node hybrid', 'rens on'])
	if mip_solver=='cplex': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.cplex_api.CPLEX_CMD(msg=solver_message,warmStart=True,timeLimit=maxtime,options=['set parallel -1','set mip tolerances mipgap ' + str(mipgap)])
	if mip_solver=='gurobi': #solver_message #'set emphasis mip 3','set threads 4', 
		solver=pulp.apis.GUROBI_CMD(msg=solver_message,warmStart=True,options=[("MIPGap",mipgap),("TimeLimit",maxtime)])
	solver.setTmpDir() #=mip_file_path
	solver.actualSolve(prob)
	#if os.path.isfile(mip_mst_file): os.remove(mip_mst_file)
	if prob.status<=0:
	   print "prob.status<0..."
	   return prob.status #failer
	node_groups=[-1 for x in range(num_units)]
	centersID=[-1 for x in range(num_districts)]
	for v in prob.variables():
		if (v.varValue >= 0.99):
			items=v.name.split('_')
			i=int(items[1])
			k=region_pool[i][4]
			#print k,costs[i],facilityCost[k]
			centersID[k]=facilityCandidate[k]
			for x in region_pool[i][0]:
				node_groups[x]=k
	a=[ x for x in centersID if x>=0]
	print "spp locs:",len(a),a
	update_district_info()
	#for i in range(num_districts): 
	#	 if district_info[i][1] >0: print i,district_info[i],facilityCost[i]
	#print 
	return 1 #success
	
def pop_selection(population):
	population1=copy.deepcopy(population)
	population1.sort(key=lambda x:x[0])
	population2=[] #delete identical solution
	#sol=[best_biobjective_global,best_centersID_global[:],best_solution_global[:],best_objective_global,best_objective_fcost_global,best_overload_global,0]
	#population2.append(copy.deepcopy(sol))
	population2.append(copy.deepcopy(population1[0]))
	sdiff=2
	'''if location_problem==3:
		sdiff=max_num_facility/20
		if sdiff<3: sdiff=3
	if max_num_facility>30:
		sdiff=4'''
	for x in population1:
		issimilar=0
		for y in population2:
			rlist=[i for i in range(num_districts) if x[1][i] != y[1][i]]
			if len(rlist)>=sdiff: continue
			else:
				if location_problem>=1:
					issimilar=1
					break
			ulist=[i for i in range(num_units) if x[2][i] != y[2][i]]
			#diffpop=sum(nodes[i][3] for i in ulist)
			#if len(ulist)<min(num_units*1.0/num_districts,num_units/30.0) and diffpop*100.0/total_pop < min(3.0,100.0/num_districts): #100.0/num_districts: #<5%
			#print len(ulist),
			if len(ulist)<num_units*(solution_similarity_limit/100.0):
				issimilar=1
				break
		if issimilar==0:
			population2.append(copy.deepcopy(x))
		#if len(population2)>=min(multi_start_count*3,10):
		#	 break
	return population2


def update_centers():
	global node_groups
	global centersID
	global time_update_centers
	if envy_service_objective==1:
		return update_center_pmp_envy()
	if location_problem==1 or location_problem==0: return
	t=time.time()
	obj=biobjective
	sol=[-1 for x in range(num_units)]
	centers=[]
	for k in range(num_districts):
		if centersID[k]<0: continue
		kn,ulist=update_center(k)
		if kn==-1:
			print "update center error:",[k,sum(1 for x in range(num_units) if node_groups[x]==k)]," ->", [kn,len(ulist)]
			print NearFacilityList[k][:10],ulist
			kn=k
		if location_problem==3 and centersID[kn]>=0 and k!=kn:
			print "update center error: new center is already used:",k,kn
			kn=k
		if len(ulist)==0:
			print "update center error: ulist is empty:",k,kn,ulist
			kn=k
		for x in ulist: sol[x]=kn
		centers.append(kn)
		centersID[k]=-1
	node_groups=sol[:]
	for k in centers:
		centersID[k]=facilityCandidate[k]
	if location_problem==3 and spatial_contiguity==0:
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break
	obj=biobjective
	update_district_info()
	update_best_solution()
	#print "updatecenters",biobjective-obj
	time_update_centers+=time.time()-t

	#print obj,obj-biobjective
def update_center_pmp_envy():
	global node_groups
	global centersID
	global time_update_centers
	t=time.time()
	obj=biobjective
	sol=[-1 for x in range(num_units)]
	centers=[]
	for k in range(num_districts):
		if centersID[k]==-1: continue
		kn,ulist=update_center_envy(k)
		if kn!=k:
			for x in ulist: node_groups[x]=kn
			centersID[kn]=facilityCandidate[kn]
			centersID[k]=-1
	time_update_centers+=time.time()-t

def update_center_envy(k):
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	best_cost=sum(nodedik[x][k] for x in ulist)*travel_distance_weight
	for u in ulist:
		d=nodedij[u][k]
		if d>envy_service_distance and envy_service_objective==1:
			best_cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
		if d>envy_service_distance and envy_service_objective==4:
			best_cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)
	best_center=k
	for i in range(num_districts):
		cost=sum(nodedik[x][i] for x in ulist)*travel_distance_weight
		for u in ulist:
			d=nodedij[u][i]
			if d>envy_service_distance and envy_service_objective==1:
				cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)*(d-envy_service_distance)
			if d>envy_service_distance and envy_service_objective==4:
				cost+=nodes[u][3]*envy_objective_weight*(d-envy_service_distance)
		if cost<best_cost:
			best_cost=cost
			best_center=i
	return best_center,ulist

def update_center(k):
	if location_problem==3: #pmp
		return update_center_pmp(k)
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	best_cost=sum(nodedik[x][k] for x in ulist)
	best_center=k
	for i in range(num_districts):
		demand=district_info[i][1]
		if facilityCapacity[i]<demand: continue
		cost=sum(nodedik[x][i] for x in ulist)
		if cost<best_cost:
			best_cost=cost
			best_center=i
	return best_center,ulist
def update_center_pmp(k): #need debug for PMP with few cands
	ulist=[x for x in range(num_units) if node_groups[x]==k]
	if ulist==[]: return k,[]
	best_cost=MAXNUMBER
	best_center=-1
	if k not in ulist:
		for i in NearFacilityList[k]:
			if i not in ulist: continue
			cost=sum(nodedik[x][i] for x in ulist)
			if cost<best_cost:
				best_cost=cost
				best_center=i
		return best_center,ulist
		
	for i in NearFacilityList[k][:min(num_districts/10,100)]:
		if i not in ulist: continue
		cost=sum(nodedik[x][i] for x in ulist)
		if cost<best_cost:
			best_cost=cost
			best_center=i
	return best_center,ulist



def search_stat():
	arcpy_print("----------------search statistics----------------------")
	arcpy_print("one unit move, move and time: "+ str(count_op[0])+ ", " +str(time_op[0]) )
	arcpy_print("two unit move, move and time: "+ str(count_op[1])+ ", " +str(time_op[1]) )
	arcpy_print("three unit move, move and time: "+ str(count_op[2])+ ", " +str(time_op[2]) )
	arcpy_print("location subproblem time: "+ str(time_LNS1) )
	arcpy_print("reassign subproblem time: "+ str(time_LNS2) )
	arcpy_print("location swap time: "+ str(time_location[0]) )
	arcpy_print("location drop time: "+ str(time_location[1]) )
	arcpy_print("location add time: "+ str(time_location[2]) )
	arcpy_print("location add-drop time: "+ str(time_location[3]) )
	arcpy_print("location multi-exchange time: "+ str(time_location[4]) )
	arcpy_print("r_r_reselect_location_pmp time: "+ str(time_location[5]) )
	arcpy_print("location TB heur. time: "+ str(time_location[7]) )
	arcpy_print("TB_Whitaker time: "+str(time_Whitaker))
	arcpy_print("location PMP sub_mip time: "+ str(time_location[8]) )
	arcpy_print("location CFLP sub_mip time: "+ str(time_location[9]) )
	arcpy_print("location PMP TB time: "+ str(time_pmp_re_location) )
	arcpy_print("repair time: "+ str(time_repair) )
	arcpy_print("check edge unit time: "+str(time_check_edge_unit))
	arcpy_print("update_centers time: "+ str(time_update_centers) )
	arcpy_print("spp regions: "+ str(len(region_pool)) )
	arcpy_print("spp pooling time: "+ str(time_spp) )
	arcpy_print("connectivity check time: "+ str(time_check))
	arcpy_print("time for ruin and recreate: " + str(time_ruin_recreate))
	#if spatial_contiguity==1:
	#	 sta=check_solution_continuality_feasibility(best_solution_global)
	#	 arcpy_print("solution on continuality (0 no, 1 yes) : "+str(sta))
	arcpy_print("----------------end of search statistics----------------")
 

def print_equality_measures():
	#print "-----------equality measures---------------"
	update_district_info()
	maxd=0.0
	mind=MAXNUMBER
	maxdev=0.0
	avgd=objective/total_pop
	absdev=0.0
	stddev=0.0
	Theil=0.0
	schutz=0.0
	upperVar=0.0
	lowerVar=0.0
	upperVarD=0.0
	lowerVarD=0.0
	upperMad=0.0
	for i in range(num_units): 
		k=node_groups[i]
		dis=nodedij[i][k]
		w=nodes[i][3]
		absdev+=w*abs(dis-avgd)
		stddev+=w*(dis-avgd)*(dis-avgd)
		if dis>maxd: maxd=dis
		if dis<mind: mind=dis
		if abs(dis-avgd)>maxdev: maxdev=abs(dis-avgd)
		'''if dis>0:
			a=dis*math.log(dis)-avgd*math.log(avgd)
			Theil+=w*a*a
		else:
			a=avgd*math.log(avgd)
			Theil+=w*a*a'''
		if dis>0:
			a=math.log(dis/avgd)
			Theil+=w*dis*a
		schutz+=w*abs(dis-avgd)
		if dis>avgd:
			upperVar+=w*(dis-avgd)*(dis-avgd)
			#upperVarD+=w*(dis-envy_service_distance)*(dis-envy_service_distance)
			upperMad+=w*(dis-avgd)
		else:
			lowerVar+=w*(dis-avgd)*(dis-avgd)
			#lowerVarD+=w*(dis-envy_service_distance)*(dis-envy_service_distance)
	equality_measures={}
	equality_measures["Max"]= maxd
	equality_measures["Range"]=maxd-mind
	equality_measures["Mean"]=avgd
	equality_measures["StdDev"]=math.sqrt(stddev/total_pop)
	#equality_measures["MaxDev"]=maxdev
	equality_measures["MAD"]=absdev/total_pop
	#equality_measures["Varance"]=stddev/total_pop
   
	Gini=0.0
	for i in range(num_units): 
		k=node_groups[i]
		d1=nodedij[i][k]
		w1=nodes[i][3]
		for j in range(num_units): 
		   k=node_groups[j]
		   d2=nodedij[j][k]
		   w2=nodes[j][3]
		   Gini+=w1*w2*abs(d1-d2)
	#print "Gini",Gini/total_pop/total_pop/2/avgd #Gini/d.num_units/d.num_units/2/avgd
	equality_measures["meanAD"]=Gini/total_pop/total_pop
	equality_measures["CV"]=equality_measures["StdDev"] /avgd
	equality_measures["SchutzI"]=schutz/total_pop/2/avgd
	equality_measures["Gini"]=Gini/total_pop/total_pop/2/avgd
	equality_measures["Theil"]= Theil/avgd/total_pop
	equality_measures["lowerVar"]=lowerVar
	#equality_measures["lowerVar2"]=lowerVarD
	equality_measures["upperVar"]=upperVar
	#equality_measures["upperVar2"]=upperVarD
	equality_measures["upperMad"]=upperMad*2/total_pop
	return equality_measures

def coverage_stat2(dlist):
	covered=[0 for x in range(len(dlist))]
	for i in range(num_units):
		k=node_groups[i]
		dis=nodedij[i][k]
		demand=nodes[i][3]
		for j in range(len(dlist)):
			if dis<=dlist[j]: covered[j]+=demand
	for i in range(len(dlist)):
		if covered[i]>0:
			print dlist[i],(covered[i]*10000/total_pop)/100.0

def coverage_stat():
	maxd=0.0
	for i in range(num_units): 
		k=node_groups[i]
		dis=nodedij[i][k]
		if dis>maxd: maxd=dis
	covered=[0 for x in range(20)]
	dlist=[0.5*x for x in range(20)]
	for i in range(num_units):
		k=node_groups[i]
		dis=nodedij[i][k]
		demand=nodes[i][3]
		for j in range(20):
			if dis<=dlist[j]: covered[j]+=demand
	#print dlist
	#print covered
	#print [x*100.0/total_pop for x in covered]
	for i in range(len(dlist)):
		#if covered==total_pop: break
		print dlist[i],(covered[i]*10000/total_pop)/100.0
		if dlist[i]>maxd: break



def sol_stat():
	fcost=objective_fcost
	sol={}
	sol["num_facility"]=sum(1 for x in centersID if x>=0)
	sol["objective"]=biobjective
	sol["TotalCost"]=objective+fcost
	sol["DCost"]=objective
	sol["Fcost"]=fcost
	sol["WeightedEnvyValue"]=objective_envy
	if objective_envy>0:
		sol["EnvyValue"]=objective_envy/envy_objective_weight
	else:
		envy=0.0
		for i in range(num_units):
			k=node_groups[i]
			d=nodedij[i][k]
			if d>envy_service_distance:
				envy+=nodes[i][3]*(d-envy_service_distance)*(d-envy_service_distance)
		sol["EnvyValue"]=envy
	sol["OverloadPenalty"]=int(objective_pentalty_on_overload/penalty_on_demand)
	sol["RMaxPenalty"]=int(objective_pentalty_on_rmax/penalty_on_demand)
	sol["RCoveragePenalty"]=int(objective_pentalty_on_covering/penalty_on_demand)
	if facilityMinimumCapacity>0:
		lowload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			lowload += max(0, facilityMinimumCapacity-district_info[k][1])
		sol["MinCap"]=lowload

	if facilityMaximumCapacity>0:
		overload=0
		for k in range(num_districts):
			if centersID[k]<=0: continue
			overload += max(0, district_info[k][1]-facilityMaximumCapacity)
		sol["MaxCap"]=overload
    
	sol["Penalty"]=penalty_on_demand
	return sol
  




def ils_pmp_envy(numf,multistarts,timelimit,myseed):
	global multi_start_count
	global seed
	global best_objective
	global best_biobjective
	global best_objective_overload
	global best_biobjective_global
	global objective
	global biobjective
	global objective_overload
	global node_groups
	global centersID
	global district_info
	#global node_neighbors
	global move_count
	global region_pool
	global pool_index
	global is_spp_modeling
	global spp_loops
	global adj_pop_loops
	global pop_dis_coeff
	global all_solutions
	global assignment_operators_selected
	global max_num_facility
	global heuristic_time_limit
	global adjust_mutation_rate
	global large_facility_cost
	global initial_solution_method
	global avg_dis_min
	global spatial_contiguity
	global location_tabu_list
	global max_exclusion_list
	max_num_facility=numf
	initialize_instance()
	print facilityCost
	heuristic_time_limit=timelimit
	all_solutions=[]
	multi_start_count=multistarts
	seed=myseed
	if seed<0:
		seed=random.randint(0,100)
	random.seed(seed)
	arcpy_print("seed: "+str(seed))
	region_pool=[]
	t=time.time()
	ga_time=0.0
	best_biobjective_global = MAXNUMBER
	best_biobjective = MAXNUMBER
	district_info = [[0,0.0,0,0,0] for x in range(num_districts)]
	population=[] #all
	pool_index=[]
	if is_spp_modeling>=1:
		pool_index=[[] for x in range(num_districts)]
	t_ga=time.time()
    
	for idx in range(multistarts):
		best_biobjective = MAXNUMBER
		if adaptive_number_of_facilities==1:
			n=max(5,num_districts/15)
			if max_facility_cost>0:
				n=int(max_facility_cost*num_districts/sum(facilityCost))
			add=[-2,-1,-1,0,0,0,1,1,2]                
			random.shuffle(add) 
			clist=range(num_districts)
			random.shuffle(clist)
			clist=clist[:n+add[0]]
			centersID=[-1 for x in range(num_districts)]
			for x in clist: centersID[x]=x
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]>=0:
						node_groups[i]=k
						break            
			update_envy_district_info()
			all_solutions.append([biobjective,centersID[:],node_groups[:]])
		if adaptive_number_of_facilities==0:
			ulist=[]
			sample_size=min(num_units,30*max_num_facility)
			while len(ulist)<sample_size: 
				u=random.randint(0,num_units-1)
				if u not in ulist: ulist.append(u)
			random.shuffle(ulist)
			obj,centers=k_medoids_sampling(ulist,[])
			if len(centers)!=numf: 
				print "error in generating initial solution..."
				continue
			centersID=[-1 for x in range(num_units)]
		
			for x in centers: centersID[x]=facilityCandidate[x]
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k]<0: continue
					node_groups[i]=k
					break
		if spatial_contiguity==1:
			repair_fragmented_solution()
		nf2=sum(1 for x in centersID if x>=0)
		update_envy_district_info()
		update_best_solution()
		for i in range(20):
			sta=pmp_Whitaker()
			update_envy_district_info()
			update_best_solution()
			update_region_pool_all()
			if sta!=1:break
		all_solutions.append([biobjective,centersID[:],node_groups[:]])
		nf=sum(1 for x in centersID if x>=0)
		print "init solution", idx, nf2,nf,biobjective,objective
	not_improved_global=0
	population=all_solutions
	improved_time=time.time()
	loop=-1
	while 1:
		loop+=1
		r=random.random()
		sidx = int(min(multi_start_count,len(population))* pow(r,1.5)*0.999)
		r=random.random()
		node_groups=population[sidx][2][:]
		centersID=population[sidx][1][:]
		update_envy_district_info()
		current=" current: " +str(int(population[sidx][0]))+" -> "
		not_improved_global+=1
		old_ids=centersID[:]
		best_obj=best_biobjective_global
		cur_obj=biobjective
		strength=3
		if adaptive_number_of_facilities==0:
			strength=2
			maxStrength=2
			if max_num_facility >= 20:
				maxStrength=min(4, int(max_num_facility+10)/10)
			strength=random.randint(2,maxStrength)
			print strength,
			assign_ruin_recreate_pmp_envy(strength)
		#uflp_shuffle()
		if adaptive_number_of_facilities==1:
			strategy=[[0,0],[0,1],[1,0],[1,1]] 
			strategy=[[2,1],[2,3],[2,2]]
			idx=random.randint(0,len(strategy)-1)
			strength=sum(strategy[idx])
			clist=[x for x in range(num_districts) if centersID[x]<0]
			if len(clist)<=strategy[idx][0]: continue
			random.shuffle(clist)
			for x in range(strategy[idx][0]):
				k=clist[x]
				centersID[k]=facilityCandidate[k]
				for i in range(num_units):
					k1=node_groups[i]
					if nodedij[i][k1]>nodedij[i][k]:
						node_groups[x]=k
			clist=[x for x in range(num_districts) if centersID[x]>=0]
			random.shuffle(clist)
			for x in range(strategy[idx][1]):
				k=clist[x]
				centersID[k]=-1
				ulist=[y for y in range(num_units) if node_groups[y]==k]
				for i in ulist:
					for k in NearFacilityList[i]:
						if centersID[k]>=0:
							node_groups[i]=k
							break
			update_envy_district_info()
		#end if uflp suffule        
		if spatial_contiguity==1:
			repair_fragmented_solution()
		imploop=max(10,strength*5)
		#imploop=100 
		rr_obj=biobjective
		for idx in range(imploop):
			sta=pmp_Whitaker()
			#sta=pmp_Whitaker()
			for i in range(num_units):
				for k in NearFacilityList[i]:
					if centersID[k] >=0:
						node_groups[i]=k
						break
			update_envy_district_info()
			update_best_solution()
			update_region_pool_all()
			if sta!=1:
				#print idx,
				break
			#print i,sta,int(biobjective), int(objective),int(objective_fcost)
		print idx,
		if adaptive_number_of_facilities==0: update_center_pmp_envy()
		if spatial_contiguity==1:
			repair_fragmented_solution()
		update_envy_district_info()
		update_best_solution()
		update_region_pool_all()
			
		s=""
		if biobjective<best_obj:  #0.1%
			#del population[sidx]
			s="*"
			impp=((biobjective-best_obj)/biobjective)*1000 #-0.1%
			not_improved_global+=int(max_loops_solution_not_improved*impp)
			if not_improved_global<0: not_improved_global=0
			#population.append([biobjective,centersID[:],node_groups[:]])
		elif biobjective<cur_obj: 
			#del population[sidx]
			s="#"
			#population.append([biobjective,centersID[:],node_groups[:]])
		else: 
			s="-" 
			#del population[sidx]
		population.append([biobjective,centersID[:],node_groups[:]])
		population.sort(key=lambda x:x[0])
		population=pop_selection(population)
		if len(population)>max(10, multi_start_count*2):
			population.pop()
		bnf=sum(1 for x in best_centersID_global if x>=0)
		s+="Search loop "+str(loop) + " best: " +str(bnf)+" "+str(int(best_biobjective_global))+" "+str(int(best_objective_global))
		nf=sum(1 for x in centersID if x>=0)
		s+=current + str(nf)+" "+str(int(biobjective))+" "+str(int(objective))+" "+str(int(objective_fcost))
		s+= " Info: " +str(len(population))+" " +str(not_improved_global)+ " "+str(int(time.time()-t_ga))
		s+= " Imp: "+ str(int(biobjective-rr_obj))
		arcpy_print(s)
		if not_improved_global >= max_loops_solution_not_improved: break
		#while len(population)>multi_start_count*5:
		#	 population.pop()
		all_solutions=population
		if time.time()-t_ga > heuristic_time_limit:	 break
	#post procedure

	population.sort(key=lambda x:x[0])
	node_groups=best_solution_global[:] #population[0][2][:]
	centersID=best_centersID_global[:]
	update_envy_district_info()
	ga_time=time.time()-t_ga
	print "Heuristic solution:",biobjective,objective_fcost,objective,objective_overload,ga_time
	t_spp=time.time()
	if is_spp_modeling>=1:
		arcpy_print("SPP modelling..."+str(len(region_pool)) )
		sppmodel((time.time()-t_ga)/10,0.000001)
		for i in range(num_units):
			for k in NearFacilityList[i]:
				if centersID[k]>=0:
					node_groups[i]=k
					break
		update_envy_district_info()
		#update_centers()
		update_best_solution()
		population.append([biobjective,centersID[:],node_groups[:],objective,objective_fcost,objective_overload,0])
		population.sort(key=lambda x:x[0])
		print "spp solution:",biobjective,objective_fcost,objective,objective_overload,time.time()-t_spp, time.time()-t_spp
		update_best_solution()
		node_groups=best_solution_global[:] #population[0][2][:]
		centersID=best_centersID_global[:]
		update_envy_district_info()

	print "final solution:",biobjective,objective_fcost,objective,objective_overload
	population.sort(key=lambda x:x[0])
	all_solutions=population
	#sta=check_solution_continuality_feasibility(node_groups)
	#print "Areal continuality(1 yes, 0 no):",sta
	#if spatial_contiguity==1:
	#	 if sta==0:	   return "infeasible final solution: continuality"
	##noprint "time",time.time()-t
	#search_stat()
	#print "location_tabu_list",len(location_tabu_list)
	return [best_biobjective_global,best_objective_global,best_overload_global,centersID,best_solution_global]
