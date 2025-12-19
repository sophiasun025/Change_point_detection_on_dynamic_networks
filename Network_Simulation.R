source("/Users/sophiasun/networkcp/functions_network_cp.R")
source("/Users/sophiasun/networkcp/network_generation_models.R")

sig=sig_gkcp=sig_gaussian=sig_gaussian_perm=sig_graphlet=0
tauhat1=tauhat2=tauhat3=tauhat4=tauhat5=tauhat6=c()



#Set parameters
n=200
setting=4
n0=n*0.05
n1=n-n0
temp=n0:n1
if(setting==1){
  p1=c(0.1,0.3,0.5,0.6,0.7)
  param=list()
  param$p_diag=p1
  param$p_diag2=p1+0.01
  param$p_off=p1
  param$p_off2=p1+0.01
  tau=rep(50,length(p1))
  n2=rep(n,length(p1))
  b1=c(25,25)
  b2=c(25,25)
}
if(setting==2){
  p1=c(0.2,0.3,0.4,0.5,0.7)
  param=list()
  param$p_diag=p1
  param$p_diag2=p1+0.05
  param$p_off=rep(0.3,length(p1))
  param$p_off2=rep(0.3,length(p1))
  tau=rep(50,length(p1))
  n2=rep(n,length(p1))
  b1=rep(10,length(p1))
  b2=rep(10,length(p1))
}
if(setting==3){
  p1=c(0.2,0.4,0.5,0.6,0.7)
  param=list()
  param$p_diag=p1
  param$p_diag2=p1+0.05
  param$p_off=p1
  param$p_off2=p1
  tau=rep(50,length(p1))
  n2=rep(n,length(p1))
  b1=rep(10,5)
  b2=rep(10,5)
}
if(setting==4){
  param=list()
  param$p_diag=c(0.05,0.05)
  param$p_diag2=param$p_diag+0.01
  param$p_off=rep(0.03,2)
  param$p_off2=param$p_off-0.01
  tau=c(50,100)
  n2=n1*2
  b1=c(25,25) #blocksize
  b2=c(25,25) #blocksize
}
J <- length(param$p_diag)
results <- list(
  mtype         = list(sig_only = integer(J), sig_accurate = integer(J)),
  sixmin        = list(sig_only = integer(J), sig_accurate = integer(J)),
  gaussian_fast = list(sig_only = integer(J), sig_accurate = integer(J)),
  gaussian      = list(sig_only = integer(J), sig_accurate = integer(J)),
  graph         = list(sig_only = integer(J), sig_accurate = integer(J))
)

for (j in 1:length(param$p_diag)){
    for (i in 1:100){
      #toydata=generate_ergm_data(100,c(-2,0.2),c(-2,0.205),50,100)
      #toydata=generate_rgg_data(0.4,0.41,50,100,FALSE,150)
      toydata=generate_toy_data(param$p_diag[j],param$p_diag2[j],param$p_off[j],param$p_off2[j],tau[j],n2[j],b1,b2)
      K1=toydata[[1]]
      K2=toydata[[2]]
      #GKCP=calculate_statistic_new(K1,K2,n)
      
      #permutation p-value for MType
      p_perm=permpval2(n,K1,K2,B=1000)
      
      #p-value approx for 6min
      scanZ=calculate_statistic_new_separate(K1,K2,0.5,2,n)
      GKCP=scanZ$GKCP$scan
      p=pval1(n,K1,K2,scanZ,0.5,2)
      pvec1=c(p$Z_D1,p$Z_W1_r1,p$ZW1_r2,p$ZD2,p$ZW2_r1,p$ZW2_r2)#6min
      
      gaussian=kerseg1(n, K1,r1=0.5,r2=2, pval.perm=TRUE,B=1000)#GKCP Gaussian
      graphlet=kerseg1(n, K2, r1=0.5,r2=2,pval.perm=TRUE,B=1000)#GKCP Graph
      
      if(6*min(pvec1)<=0.05){
        sig=sig+1
        tauhat1=c(tauhat1,temp[which.max(GKCP[n0:n1])])
      }
  
      if(p_perm$GKCP$pval<=0.05){
        sig_gkcp=sig_gkcp+1
        tauhat3=c(tauhat3,temp[which.max(GKCP[n0:n1])])
      }
      
      if(gaussian$perm$GKCP<=0.05){
        sig_gaussian_perm=sig_gaussian_perm+1
        tauhat4=c(tauhat4,gaussian$tauhat)
        
      }
      if (gaussian$appr$fGKCP1_bon<=0.05){
        sig_gaussian=sig_gaussian+1
        tauhat6=c(tauhat6,gaussian$tauhat)
      }
      
      if(graphlet$perm$GKCP<=0.05){
        #if (graphlet$appr$fGKCP1_bon<=0.05){
        sig_graphlet=sig_graphlet+1
        tauhat5=c(tauhat5,graphlet$tauhat)
      }
      print(i)
    }

results$mtype$sig_only[j]=sig_gkcp
results$mtype$sig+accurate[j]=length(which(abs(tauhat3-tau)<=0.05*n))

results$sixmin$sig_only[j]=sig
results$sixmin$sig+accurate[j]=length(which(abs(tauhat1-tau)<=0.05*n))

results$gaussian_fast$sig_only[j]=sig_gaussian
results$gaussian_fast$sig+accurate[j]=length(which(abs(tauhat6-tau)<=0.05*n))

results$gaussian$sig_only[j]=sig_gaussian_perm
results$gaussian$sig+accurate[j]=length(which(abs(tauhat4-tau)<=0.05*n))

results$graph$sig_only[j]=sig_graphlet
results$graph$sig+accurate[j]=length(which(abs(tauhat5-tau)<=0.05*n))

print('mtype')
sig_gkcp #mtype
length(which(abs(tauhat3-tau)<=0.05*n))

print('6min')
sig #6min
length(which(abs(tauhat1-tau)<=0.05*n))

print('gaussian FAST')
sig_gaussian
length(which(abs(tauhat6-tau)<=0.05*n))

print('gaussian')
sig_gaussian_perm
length(which(abs(tauhat4-tau)<=0.05*n))

print('graph')
sig_graphlet
length(which(abs(tauhat5-tau)<=0.05*n))

}


