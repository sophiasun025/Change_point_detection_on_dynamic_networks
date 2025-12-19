                                            

library(raster)
library(frechet)
require(graphkernels)
library(reshape)                                             
library(igraph)                                   
library(ggplot2) 
library(kerSeg)
library(MASS)
library(ergm)
library(e1071)
library(combinat)
library(network)

DW_third_moment = function(n, K, r1=0.5, r2=2) {
  t = 1:n
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  p4 = p3*(t-4)/(n-4)
  p5 = p4*(t-5)/(n-5)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  q4 = q3*(n-t-4)/(n-4)
  q5 = q4*(n-t-5)/(n-5)
  
  f1 = t*(t-1)*(n-t)*(n-t-1)/n/(n-1)/(n-2)/(n-3)
  f2 = f1*(t-2)/(n-4)
  f3 = f2*(t-3)/(n-5)
  
  g1 = f1
  g2 = g1*(n-t-2)/(n-4)
  g3 = g2*(n-t-3)/(n-5)
  
  R0 = sum(K)
  R1 = sum(K^2)
  R_temp = rowSums(K)
  R_temp1 = rowSums(K^2)
  R_temp2 = R_temp^2 - R_temp1
  R2 = sum(R_temp2)
  temp1 = sum(K^3)
  temp2 = sum( R_temp*R_temp1 ) - temp1
  temptemp = skew(K, R_temp, R_temp2, R0, R2)
  temp3 = 2*temptemp[1]
  temp4 = 2*temptemp[2]
  temp5 = 2*temptemp[3]
  temp6 = 2*temptemp[4]
  temp7 = 2*temptemp[5]
  temp8 = sum(K)^3 - 4*temp1 - 24*temp2 - 8*temp3 - 6*temp4 - 8*temp5 - 24*temp6 - 12*temp7
  
  # alpha^3
  EKx3 = ( 4*temp1*p1+24*temp2*p2+8*temp3*p2+6*temp4*p3+8*temp5*p3+24*temp6*p3+12*temp7*p4+temp8*p5 )/t/t/t/(t-1)/(t-1)/(t-1)
  # beta^3
  EKy3 = ( 4*temp1*q1+24*temp2*q2+8*temp3*q2+6*temp4*q3+8*temp5*q3+24*temp6*q3+12*temp7*q4+temp8*q5 )/(n-t)/(n-t)/(n-t)/(n-t-1)/(n-t-1)/(n-t-1)
  # alpha^2beta
  EKx2Ky = ( 2*temp4*f1+4*temp7*f2+temp8*f3 )/t/t/(t-1)/(t-1)/(n-t)/(n-t-1)
  # beta^2alpha
  EKxKy2 = ( 2*temp4*g1+4*temp7*g2+temp8*g3 )/t/(t-1)/(n-t)/(n-t)/(n-t-1)/(n-t-1)
  
  u.D = t*(t-1)/(n*(n-1))
  v.D = -(n-t)*(n-t-1)/(n*(n-1))
  u.W1 = r1*t/n
  v.W1 = (n-t)/n
  u.W2 = r2*t/n
  v.W2 = (n-t)/n
  
  ED.3 = u.D^3*EKx3 + 3*u.D^2*v.D*EKx2Ky + 3*u.D*v.D^2*EKxKy2 + v.D^3*EKy3
  EW1.3 = u.W1^3*EKx3 + 3*u.W1^2*v.W1*EKx2Ky + 3*u.W1*v.W1^2*EKxKy2 + v.W1^3*EKy3
  EW2.3 = u.W2^3*EKx3 + 3*u.W2^2*v.W2*EKx2Ky + 3*u.W2*v.W2^2*EKxKy2 + v.W2^3*EKy3
  
  return( list(ED.3 = ED.3, EW1.3 = EW1.3, EW2.3 = EW2.3) )
}


calculate_statistic_new_separate<-function(K1,K2,r1=0.5,r2=2,n,n0=ceiling(0.05*n), n1=floor(0.95*n)){
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  t = 1:n
  temp = n0:n1
  R_temp1 = rowSums(K1)
  R_temp2 = rowSums(K2)
  
  K1x = K1y = rep(0, n)
  K1x[2] = sum(K1[1:2,1:2])
  K1y[2] = sum(K1[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col = K1[,i]
    add = sum(temp_col[1:i])
    subtract = R_temp1[i] - add
    K1x[i] = (K1x[i-1] + 2*add)
    K1y[i] = (K1y[i-1] - 2*subtract)
  }
  
  K1x=K1x/(t*(t-1))
  K1y=K1y/((n-t)*(n-t-1))
  
  
  K2x = K2y = rep(0, n)
  K2x[2] = sum(K2[1:2,1:2])
  K2y[2] = sum(K2[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col2 = K2[,i]
    add = sum(temp_col2[1:i])
    subtract = R_temp2[i] - add
    K2x[i] = (K2x[i-1] + 2*add)
    K2y[i] = (K2y[i-1] - 2*subtract)
  }
  
  K2x=K2x/(t*(t-1))
  K2y=K2y/((n-t)*(n-t-1))
  
  R0_1 = sum(K1)
  mu_K1x = R0_1/n/(n-1)
  mu_K1y = R0_1/n/(n-1)
  
  R0_2 = sum(K2)
  mu_K2x = R0_2/n/(n-1)
  mu_K2y = R0_2/n/(n-1)
  
  A_2 = sum(K2^2)
  B_2 = sum(R_temp2^2) - A_2
  C_2 = R0_2^2 - 2*A_2 - 4*B_2
  
  A_1 = sum(K1^2)
  B_1 = sum(R_temp1^2) - A_1
  C_1 = R0_1^2 - 2*A_1 - 4*B_1
  
  A_cross=sum(K1*K2)
  B_cross=sum(R_temp2*R_temp1) - A_cross
  C_cross=R0_1*R0_2-2*A_cross-4*B_cross
  
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  
  var_K1x = (2*A_1*p1 + 4*B_1*p2 + C_1*p3)/t/t/(t-1)/(t-1) - mu_K1x^2
  var_K1y = (2*A_1*q1 + 4*B_1*q2 + C_1*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y^2
  cov_K1x_K1y = C_1/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K1y
  
  var_K2x = (2*A_2*p1 + 4*B_2*p2 + C_2*p3)/t/t/(t-1)/(t-1) - mu_K2x^2
  var_K2y = (2*A_2*q1 + 4*B_2*q2 + C_2*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K2y^2
  cov_K2x_K2y = C_2/n/(n-1)/(n-2)/(n-3) - mu_K2x*mu_K2y
  
  cov_K1x_K2x=(2*A_cross*p1 + 4*B_cross*p2 + C_cross*p3)/t/t/(t-1)/(t-1) - mu_K2x*mu_K1x
  cov_K1y_K2y=(2*A_cross*q1 + 4*B_cross*q2 + C_cross*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y*mu_K2y
  cov_K1x_K2y=cov_K1y_K2x=C_cross/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K2y
  
  # test statistic D1
  D.weight1 = t*(t-1)/(n*(n-1))
  D.weight2 = -(n-t)*(n-t-1)/(n*(n-1))
  
  mean.D1 = mu_K1x*D.weight1 + mu_K1y*D.weight2
  var.D1 = (D.weight1^2)*var_K1x + (D.weight2^2)*var_K1y + 2*D.weight1*D.weight2*cov_K1x_K1y
  D1=K1x*D.weight1 + K1y*D.weight2
  
  # test statistic W1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1 = mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1 = var_K1x*w.weight1^2 + var_K1y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K1x_K1y
  W1 = K1x*w.weight1 + K1y*w.weight2
  
  
  # test statistic W1_r1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1_r1 = r1*mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1_r1 = var_K1x*w.weight1^2*r1^2 + var_K1y*w.weight2^2 + 2*r1*w.weight1*w.weight2*cov_K1x_K1y
  W1_r1 = K1x*w.weight1*r1 + K1y*w.weight2
  
  # test statistic W1_r2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1_r2 = r2*mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1_r2 = var_K1x*w.weight1^2*r2^2 + var_K1y*w.weight2^2 + 2*r2*w.weight1*w.weight2*cov_K1x_K1y
  W1_r2 = K1x*w.weight1*r2 + K1y*w.weight2
  
  # test statistic D2
  mean.D2 = mu_K2x*D.weight1 + mu_K2y*D.weight2
  var.D2 = (D.weight1^2)*var_K2x + (D.weight2^2)*var_K2y + 2*D.weight1*D.weight2*cov_K2x_K2y
  D2 = K2x*D.weight1 + K2y*D.weight2
  
  
  # test statistic W2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2 = mu_K2x*w.weight1 + mu_K2y*w.weight2
  var.W2 = var_K2x*w.weight1^2 + var_K2y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K2x_K2y
  W2 = K2x*w.weight1 + K2y*w.weight2
  
  # test statistic W2_r1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2_r1 = r1*mu_K2x*w.weight1 + mu_K2y*w.weight2
  var.W2_r1 = var_K2x*w.weight1^2*r1^2 + var_K2y*w.weight2^2 + 2*r1*w.weight1*w.weight2*cov_K2x_K2y
  W2_r1 = r1*K2x*w.weight1 + K2y*w.weight2
  
  # test statistic W2_r2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2_r2 = mu_K2x*w.weight1*r2 + mu_K2y*w.weight2
  var.W2_r2 = var_K2x*w.weight1^2*r2^2 + var_K2y*w.weight2^2 + 2*r2*w.weight1*w.weight2*cov_K2x_K2y
  W2_r2 = K2x*w.weight1*r2 + K2y*w.weight2
  
  cov_w1_w2 <- w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*w.weight1*w.weight2*cov_K1x_K2y
  cov_D1_D2 <- D.weight1^2*cov_K1x_K2x + D.weight2^2*cov_K1y_K2y + 2*D.weight1*D.weight2*cov_K1x_K2y
  
  cov_w1_w2_r1 <- r1^2*w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*r1*w.weight1*w.weight2*cov_K1x_K2y
  cov_w1_w2_r2 <- r2^2*w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*r2*w.weight1*w.weight2*cov_K1x_K2y
  
  #weight x (D)
  t2=(A_2+B_2)-(2*A_2+4*B_2+C_2)/n
  t1=(A_1+B_1)-(2*A_1+4*B_1+C_1)/n
  t_cross=(A_cross+B_cross)-(2*A_cross+4*B_cross+C_cross)/n
  x = (t2-t_cross)/(t1-t_cross)
  
  #weight a (W)
  m1=(n-2)*A_1+(2*A_1+4*B_1+C_1)/(n-1)-2*(A_1+B_1)
  m2=(n-2)*A_2+(2*A_2+4*B_2+C_2)/(n-1)-2*(A_2+B_2)
  m_cross=(n-2)*A_cross+(2*A_cross+4*B_cross+C_cross)/(n-1)-2*(A_cross+B_cross)
  a = (m2-m_cross)/(m1-m_cross)
  
  #Standardized W1_r1
  ZW1_r1= (W1_r1-mean.W1_r1)/sqrt(var.W1_r1)
  #Standardized W1_r2
  ZW1_r2= (W1_r2-mean.W1_r2)/sqrt(var.W1_r2)
  #Standardized W1
  ZW1= (W1-mean.W1)/sqrt(var.W1)
  #Standardized D1
  ZD1=(D1-mean.D1)/sqrt(var.D1)
  #Standardized W2_r1
  ZW2_r1= (W2_r1-mean.W2_r1)/sqrt(var.W2_r1)
  #Standardized W2_r2
  ZW2_r2= (W2_r2-mean.W2_r2)/sqrt(var.W2_r2)
  #Standardized W2
  ZW2= (W2-mean.W2)/sqrt(var.W2)
  #Standardized D2
  ZD2=(D2-mean.D2)/sqrt(var.D2)
  
  scanZ=list()
  scanZ$ZW1_r1$scan=ZW1_r1
  scanZ$ZW1_r1$Zmax=max(ZW1_r1[n0:n1])
  scanZ$ZW1_r1$tauhat=temp[which.max(ZW1_r1[n0:n1])]
  
  scanZ$ZW1_r2$scan=ZW1_r2
  scanZ$ZW1_r2$Zmax=max(ZW1_r2[n0:n1])
  scanZ$ZW1_r2$tauhat=temp[which.max(ZW1_r2[n0:n1])]
  
  scanZ$ZW1$scan=ZW1
  scanZ$ZW1$Zmax=max(ZW1[n0:n1])
  scanZ$ZW1$tauhat=temp[which.max(ZW1[n0:n1])]
  
  scanZ$ZD1$scan=ZD1
  scanZ$ZD1$Zmax=max(abs(ZD1[n0:n1]))
  scanZ$ZD1$tauhat=temp[which.max(abs(ZD1[n0:n1]))]
  
  scanZ$ZW2_r1$scan=ZW2_r1
  scanZ$ZW2_r1$Zmax=max(ZW2_r1[n0:n1])
  scanZ$ZW2_r1$tauhat=temp[which.max(ZW2_r1[n0:n1])]
  
  scanZ$ZW2_r2$scan=ZW2_r2
  scanZ$ZW2_r2$Zmax=max(ZW2_r2[n0:n1])
  scanZ$ZW2_r2$tauhat=temp[which.max(ZW2_r2[n0:n1])]
  
  scanZ$ZW2$scan=ZW2
  scanZ$ZW2$Zmax=max(ZW2[n0:n1])
  scanZ$ZW2$tauhat=temp[which.max(ZW2[n0:n1])]
  
  scanZ$ZD2$scan=ZD2
  scanZ$ZD2$Zmax=max(abs(ZD2[n0:n1]))
  scanZ$ZD2$tauhat=temp[which.max(abs(ZD2[n0:n1]))]
  
  scanZ$weightW=a
  scanZ$weightD=x
  
  #Standardized W1-W2
  Diff_W=(W1-W2-mean.W1+mean.W2)/sqrt(var.W1+var.W2-2*cov_w1_w2)
  
  #Standardized D1-D2
  Diff_D=(D1-D2-mean.D1+mean.D2)/sqrt(var.D1+var.D2-2*cov_D1_D2)
  
  #Standardized aW1+W2
  Sum_W=(a*W1+W2-a*mean.W1-mean.W2)/sqrt(a^2*var.W1+var.W2+2*a*cov_w1_w2)
  
  #Standardized xD1+D2
  Sum_D=(x*D1+D2-x*mean.D1-mean.D2)/sqrt(x^2*var.D1+var.D2+2*x*cov_D1_D2)
  
  #weighted sum of D1  and D2
  scanZ$D_sum$scan=Sum_D
  scanZ$D_sum$max=max(abs(Sum_D[n0:n1]))
  scanZ$D_sum$tauhat=temp[which.max(abs(Sum_D[n0:n1]))]
  
  #difference of D1 and D2
  scanZ$D_diff$scan=Diff_D
  scanZ$D_diff$max=max(abs(Diff_D)[n0:n1])
  scanZ$D_diff$tauhat=temp[which.max(abs(Diff_D)[n0:n1])]
  
  #diff of W1  and W2 
  scanZ$W_diff$scan=Diff_W
  scanZ$W_diff$max=max(abs(Diff_W)[n0:n1])
  scanZ$W_diff$tauhat=temp[which.max(abs(Diff_W)[n0:n1])]
  
  #weighted sum of W1  and W2 
  scanZ$W_sum$scan=Sum_W
  scanZ$W_sum$max=max(Sum_W[n0:n1])
  scanZ$W_sum$tauhat=temp[which.max((Sum_W)[n0:n1])]

  #GKCP
  scanZ$GKCP$scan=Sum_W^2+Sum_D^2+Diff_W^2+Diff_D^2
  scanZ$GKCP$max=max((Sum_W^2+Sum_D^2+Diff_W^2+Diff_D^2)[n0:n1])
  scanZ$GKCP$tauhat=temp[which.max((Sum_W^2+Sum_D^2+Diff_W^2+Diff_D^2)[n0:n1])]
  
  #added for debugging
  scanZ$W1$scan=W1-mean.W1
  scanZ$W2$scan=W2-mean.W2
  scanZ$D1$scan=D1-mean.D1
  scanZ$D2$scan=D2-mean.D2
  scanZ$W_diff0$scan=W1-W2-mean.W1+mean.W2
  scanZ$D_diff0$scan=D1-D2-mean.D1+mean.D2
  
  scanZ$W_sum0$scan=a*W1+W2-a*mean.W1-mean.W2
  scanZ$D_sum0$scan=x*D1+D2-x*mean.D1-mean.D2
  #
  
  #third_moment_K1= DW_third_moment(n,K1,r1=r1,r2=r2)
  #third_moment_K2= DW_third_moment(n,K2,r1=r1,r2=r2)
  
  #skewness of Z_D1
  #ZD1.3=(third_moment_K1$ED.3-3*mean.D1*var.D1-(mean.D1^3))/sqrt(var.D1)^3
  #scanZ$ZD1$skewness=ZD1.3
  
  #skewness of Z_D2
  #ZD2.3=(third_moment_K2$ED.3-3*mean.D2*var.D2-(mean.D2^3))/sqrt(var.D2)^3
  #scanZ$ZD2$skewness=ZD2.3
  
  #skewness of Z_w1_r1
  #ZW1_r1.3=(third_moment_K1$EW1.3-3*mean.W1_r1*var.W1_r1-(mean.W1_r1^3))/sqrt(var.W1_r1)^3
  #scanZ$ZW1_r1$skewness=ZW1_r1.3
  #skewness of Z_w2_r1
  #ZW2_r1.3=(third_moment_K2$EW1.3-3*mean.W2_r1*var.W2_r1-(mean.W2_r1^3))/sqrt(var.W2_r1)^3
  #scanZ$ZW2_r1$skewness=ZW2_r1.3
  #skewness of Z_w1_r2
  #ZW1_r2.3=(third_moment_K1$EW2.3-3*mean.W1_r2*var.W1_r2-(mean.W1_r2^3))/sqrt(var.W1_r2)^3
  #scanZ$ZW1_r2$skewness=ZW1_r2.3
  #skewness of Z_w2_r2
  #ZW2_r2.3=(third_moment_K2$EW2.3-3*mean.W2_r2*var.W2_r2-(mean.W2_r2^3))/sqrt(var.W2_r2)^3
  #scanZ$ZW2_r2$skewness=ZW2_r2.3
  return(scanZ)
}


#computes variance covariance for single kernel
compute_variance1 = function(n, K, K1,r1, r2, n0=ceiling(0.05*n), n1=floor(0.95*n)) {
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  t = 1:n
  temp = n0:n1
  
  R_temp = rowSums(K)
  
  Kx = Ky = rep(0, n)
  Kx[2] = sum(K[1:2,1:2])
  Ky[2] = sum(K[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col = K[,i]
    add = sum(temp_col[1:i])
    subtract = R_temp[i] - add
    Kx[i] = Kx[i-1] + 2*add
    Ky[i] = Ky[i-1] - 2*subtract
  }
  Kx = Kx/t/(t-1)
  Ky = Ky/(n-t)/(n-t-1)
  
  R0 = sum(K)
  mu_Kx = R0/n/(n-1)
  mu_Ky = R0/n/(n-1)
  
  R1 = sum(K^2)
  R2 = sum(R_temp^2) - R1
  R3 = R0^2 - 2*R1 - 4*R2
  
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  
  var_Kx = (2*R1*p1 + 4*R2*p2 + R3*p3)/t/t/(t-1)/(t-1) - mu_Kx^2
  var_Ky = (2*R1*q1 + 4*R2*q2 + R3*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_Ky^2
  cov_Kx_Ky = R3/n/(n-1)/(n-2)/(n-3) - mu_Kx*mu_Ky
  
  sigma<-matrix(c(var_K1x,cov_K1x_K1y,cov_K1x_K1y,var_K1y),nrow=2)
  return(sigma)
}


# compute covariance matrix for 2 kernels
compute_variance<-function(K1,K2,n,t){
  R_temp1 = rowSums(K1)
  R_temp2 = rowSums(K2)
  
  R0_1 = sum(K1)
  mu_K1x = R0_1/n/(n-1)
  mu_K1y = R0_1/n/(n-1)
  
  R0_2 = sum(K2)
  mu_K2x = R0_2/n/(n-1)
  mu_K2y = R0_2/n/(n-1)
  
  R1_2 = sum(K2^2)
  R2_2 = sum(R_temp2^2) - R1_2
  R3_2 = R0_2^2 - 2*R1_2 - 4*R2_2
  
  R1_1 = sum(K1^2)
  R2_1 = sum(R_temp1^2) - R1_1
  R3_1 = R0_1^2 - 2*R1_1 - 4*R2_1
  
  R1_cross=sum(K1*K2)
  R2_cross=sum(R_temp2*R_temp1) - R1_cross
  R3_cross=R0_1*R0_2-2*R1_cross-4*R2_cross
  
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  
  var_K1x = (2*R1_1*p1 + 4*R2_1*p2 + R3_1*p3)/t/t/(t-1)/(t-1) - mu_K1x^2
  var_K1y = (2*R1_1*q1 + 4*R2_1*q2 + R3_1*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y^2
  cov_K1x_K1y = R3_1/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K1y
  
  var_K2x = (2*R1_2*p1 + 4*R2_2*p2 + R3_2*p3)/t/t/(t-1)/(t-1) - mu_K2x^2
  var_K2y = (2*R1_2*q1 + 4*R2_2*q2 + R3_2*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K2y^2
  cov_K2x_K2y = R3_2/n/(n-1)/(n-2)/(n-3) - mu_K2x*mu_K2y
  
  cov_K1x_K2x=(2*R1_cross*p1 + 4*R2_cross*p2 + R3_cross*p3)/t/t/(t-1)/(t-1) - mu_K2x*mu_K1x
  cov_K1y_K2y=(2*R1_cross*q1 + 4*R2_cross*q2 + R3_cross*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y*mu_K2y
  cov_K1x_K2y=cov_K1y_K2x=R3_cross/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K2y
  
  
  sigma<-matrix(c(var_K1x,cov_K1x_K1y,cov_K1x_K2x,cov_K1x_K2y,
                  cov_K1x_K1y,var_K1y,cov_K1y_K2x,cov_K1y_K2y,
                  cov_K1x_K2x,cov_K1y_K2x,var_K2x,cov_K2x_K2y,
                  cov_K1x_K2y,cov_K1y_K2y,cov_K2x_K2y,var_K2y),nrow=4)
  return(sigma)
}


compute_a<-function(K1,K2,n,t){
  R0_1 = sum(K1)/(n*(n-1))
  R0_2 = sum(K2)/(n*(n-1))
  
  alpha1<-sum(K1[1:t,1:t])/(t*(t-1))
  alpha2<-sum(K2[1:t,1:t])/(t*(t-1))
  h=t+1
  beta1<-sum(K1[h:n,h:n])/((n-t)*(n-t-1))
  beta2<-sum(K2[h:n,h:n])/((n-t)*(n-t-1))
  
  return(c(alpha1-R0_1,beta1-R0_1,alpha2-R0_2,beta2-R0_2))
}


#variance and a for 1 kernel

compute_a1<-function(K1,n,t){
  R0_1 = sum(K1)/(n*(n-1))
  
  
  alpha1<-sum(K1[1:t,1:t])/(t*(t-1))
  
  h=t+1
  beta1<-sum(K1[h:n,h:n])/((n-t)*(n-t-1))
  
  
  return(c(alpha1-R0_1,beta1-R0_1))
}


compute_variance1<-function(K1,n,t){
  R_temp1 = rowSums(K1)
  
  R0_1 = sum(K1)
  mu_K1x = R0_1/n/(n-1)
  mu_K1y = R0_1/n/(n-1)
  
  R1_1 = sum(K1^2)
  R2_1 = sum(R_temp1^2) - R1_1
  R3_1 = R0_1^2 - 2*R1_1 - 4*R2_1
  
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  
  var_K1x = (2*R1_1*p1 + 4*R2_1*p2 + R3_1*p3)/t/t/(t-1)/(t-1) -mu_K1x^2
  var_K1y = (2*R1_1*q1 + 4*R2_1*q2 + R3_1*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y^2
  cov_K1x_K1y = R3_1/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K1y
  
  sigma<-matrix(c(var_K1x,cov_K1x_K1y,cov_K1x_K1y,var_K1y),nrow=2)
  return(sigma)
}



#new fast algorithm for gkcp 2 kernels

calculate_statistic_new<-function(K1,K2,n,n0=ceiling(0.1*n), n1=floor(0.9*n),r=0.5){
  output=list()
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  t = 1:n
  temp = n0:n1
  R_temp1 = rowSums(K1)
  R_temp2 = rowSums(K2)
  
  K1x = K1y = rep(0, n)
  K1x[2] = sum(K1[1:2,1:2])
  K1y[2] = sum(K1[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col = K1[,i]
    add = sum(temp_col[1:i])
    subtract = R_temp1[i] - add
    K1x[i] = (K1x[i-1] + 2*add)
    K1y[i] = (K1y[i-1] - 2*subtract)
  }
  
  K1x=K1x/(t*(t-1))
  K1y=K1y/((n-t)*(n-t-1))
  
  
  K2x = K2y = rep(0, n)
  K2x[2] = sum(K2[1:2,1:2])
  K2y[2] = sum(K2[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col2 = K2[,i]
    add = sum(temp_col2[1:i])
    subtract = R_temp2[i] - add
    K2x[i] = (K2x[i-1] + 2*add)
    K2y[i] = (K2y[i-1] - 2*subtract)
  }
  
  K2x=K2x/(t*(t-1))
  K2y=K2y/((n-t)*(n-t-1))
  
  R0_1 = sum(K1)
  mu_K1x = R0_1/n/(n-1)
  mu_K1y = R0_1/n/(n-1)
  
  R0_2 = sum(K2)
  mu_K2x = R0_2/n/(n-1)
  mu_K2y = R0_2/n/(n-1)
  
  A_2 = sum(K2^2)
  B_2 = sum(R_temp2^2) - A_2
  C_2 = R0_2^2 - 2*A_2 - 4*B_2
  
  A_1 = sum(K1^2)
  B_1 = sum(R_temp1^2) - A_1
  C_1 = R0_1^2 - 2*A_1 - 4*B_1
  
  A_cross=sum(K1*K2)
  B_cross=sum(R_temp2*R_temp1) - A_cross
  C_cross=R0_1*R0_2-2*A_cross-4*B_cross
  
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  
  var_K1x = (2*A_1*p1 + 4*B_1*p2 + C_1*p3)/t/t/(t-1)/(t-1) - mu_K1x^2
  var_K1y = (2*A_1*q1 + 4*B_1*q2 + C_1*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y^2
  cov_K1x_K1y = C_1/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K1y
  
  var_K2x = (2*A_2*p1 + 4*B_2*p2 + C_2*p3)/t/t/(t-1)/(t-1) - mu_K2x^2
  var_K2y = (2*A_2*q1 + 4*B_2*q2 + C_2*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K2y^2
  cov_K2x_K2y = C_2/n/(n-1)/(n-2)/(n-3) - mu_K2x*mu_K2y
  
  cov_K1x_K2x=(2*A_cross*p1 + 4*B_cross*p2 + C_cross*p3)/t/t/(t-1)/(t-1) - mu_K2x*mu_K1x
  cov_K1y_K2y=(2*A_cross*q1 + 4*B_cross*q2 + C_cross*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y*mu_K2y
  cov_K1x_K2y=cov_K1y_K2x=C_cross/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K2y
  
  # test statistic D1
  D.weight1 = t*(t-1)/(n*(n-1))
  D.weight2 = -(n-t)*(n-t-1)/(n*(n-1))
  
  mean.D1 = mu_K1x*D.weight1 + mu_K1y*D.weight2
  var.D1 = (D.weight1^2)*var_K1x + (D.weight2^2)*var_K1y + 2*D.weight1*D.weight2*cov_K1x_K1y
  D1=K1x*D.weight1 + K1y*D.weight2
  
  # test statistic W1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1 = mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1 = var_K1x*w.weight1^2 + var_K1y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K1x_K1y
  W1 = K1x*w.weight1 + K1y*w.weight2
  
  W1r= r*K1x*w.weight1 + K1y*w.weight2
  mean.W1r = r*mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1r = var_K1x*w.weight1^2*r^2 + var_K1y*w.weight2^2 + 2*r*w.weight1*w.weight2*cov_K1x_K1y
  
  
  # test statistic D2
  mean.D2 = mu_K2x*D.weight1 + mu_K2y*D.weight2
  var.D2 = (D.weight1^2)*var_K2x + (D.weight2^2)*var_K2y + 2*D.weight1*D.weight2*cov_K2x_K2y
  D2 = K2x*D.weight1 + K2y*D.weight2
  
  
  # test statistic W2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2 = mu_K2x*w.weight1 + mu_K2y*w.weight2
  var.W2 = var_K2x*w.weight1^2 + var_K2y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K2x_K2y
  W2 = K2x*w.weight1 + K2y*w.weight2
  
  mean.W2r = r*mu_K2x*w.weight1 + mu_K2y*w.weight2
  var.W2r = r*var_K2x*w.weight1^2 + var_K2y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K2x_K2y
  W2r = r*K2x*w.weight1 + K2y*w.weight2
  
  cov_w1_w2 <- w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*w.weight1*w.weight2*cov_K1x_K2y
  cov_D1_D2 <- D.weight1^2*cov_K1x_K2x + D.weight2^2*cov_K1y_K2y + 2*D.weight1*D.weight2*cov_K1x_K2y
  
  #weight x
  t2=(A_2+B_2)-(2*A_2+4*B_2+C_2)/n
  t1=(A_1+B_1)-(2*A_1+4*B_1+C_1)/n
  t_cross=(A_cross+B_cross)-(2*A_cross+4*B_cross+C_cross)/n
  x = (t2-t_cross)/(t1-t_cross)
  
  #weight a
  m1=(n-2)*A_1+(2*A_1+4*B_1+C_1)/(n-1)-2*(A_1+B_1)
  m2=(n-2)*A_2+(2*A_2+4*B_2+C_2)/(n-1)-2*(A_2+B_2)
  m_cross=(n-2)*A_cross+(2*A_cross+4*B_cross+C_cross)/(n-1)-2*(A_cross+B_cross)
  a = (m2-m_cross)/(m1-m_cross)
  
  #Standardized W1-W2 squared
  Diff_W_squared=(W1-W2-mean.W1+mean.W2)^2/(var.W1+var.W2-2*cov_w1_w2)
  
  #Standardized D1-D2
  Diff_D_squared=(D1-D2-mean.D1+mean.D2)^2/(var.D1+var.D2-2*cov_D1_D2)
  
  #Standardized aW1+W2
  Sum_W_squared=(a*W1+W2-a*mean.W1-mean.W2)^2/(a^2*var.W1+var.W2+2*a*cov_w1_w2)
  
  #Standardized xD1+D2
  Sum_D_squared=(x*D1+D2-x*mean.D1-mean.D2)^2/(x^2*var.D1+var.D2+2*x*cov_D1_D2)
  
  output$GKCP=(Diff_W_squared+Diff_D_squared+Sum_W_squared+Sum_D_squared)
  output$ZW1=(W1-mean.W1)/sqrt(var.W1)
  output$ZW2=(W2-mean.W2)/sqrt(var.W2)
  output$ZD1=(D1-mean.D1)/sqrt(var.D1)
  output$ZD2=(D2-mean.D2)/sqrt(var.D2)
  output$GKCP1=(W1-mean.W1)^2/(var.W1)+(D1-mean.D1)^2/(var.D1)
  output$GKCP2=(W2-mean.W2)^2/(var.W2)+(D2-mean.D2)^2/(var.D2)
  return(output)
}


#p value approximation for 6 separate statistics

rhoD = function(n, t) {
  n/2/t/(n-t)
}

# r = r1 or r2
rhoW = function(n, t, r, R0, R1, R2) {
  R3 = R0^2 - 2*R1 - 4*R2
  ft = t*(t-1)*(n-t)*(n-t-1)/n/(n-1)/(n-2)/(n-3)
  qhat = (n-t)/n 
  phat = t/n
  
  temp1 = 2*t-n+2*n*t-3*t^2
  temp2 = 3*t^2-4*n*t+2*t+n^2-n
  
  r1 = ((n-t)/(n^3*(n-1)))*(r^2*temp1 + r*t + t*(n-t-1))
  r2 = ((n-t)/(n^3*(n-1)*(n-2)))*(r^2*temp1*(t-2) + r*t*(t^2-n*t+n-2) + t*(n-t-1)*(n-2*t-2))
  
  part1 = r^2*temp1*(t-2)*(t-3)
  part2 = r*temp1*(n-t-1)*t
  part3 = r*t*(3*t^3-4*n*t^2-5*t^2+n^2*t+7*n*t-2*t-n^2-3*n+6)
  part4 = t*(n-t-1)*(3*t^2-4*n*t+10*t+n^2-5*n+6)
  r3 = ((n-t)/(n^3*(n-1)*(n-2)*(n-3)))*(part1 + part2 + part3 + part4)
  
  r0 = (t*(n-t)/(n^4*(n-1)^2))*(r^2*temp1*(t-1) + r*temp1*(n-t-1) + r*temp2*(t-1) + temp2*(n-t-1))
  
  numerator_deriv = 2*R1*r1 + 4*R2*r2 + R3*r3 - R0^2*r0
  
  vart1 = ( (r*qhat+phat)^2*(2*R1-2*R0^2/n/(n-1)) + (r^2*qhat^2*(t-2)/(n-t-1)+phat^2*(n-t-2)/(t-1)-2*r*qhat*phat)*(4*R1+4*R2-4*R0^2/n) )
  vart = ft*vart1
  
  vart_deriv1 = (4*t^3-6*n*t^2+2*n^2*t+2*n*t-2*t-n^2+n)/n/(n-1)/(n-2)/(n-3)
  vart_deriv21 = ( 2*(1-r)*(r*(n-t)+t)/n/n )
  vart_deriv22 = r^2*(2*t^2-3*n*t+t+n^2+n-4)*(n-t)/(n-t-1)/(n-t-1)
  vart_deriv23 = t*(-2*t^2+n*t+t-2*n+4)/(t-1)/(t-1)
  
  vart_deriv = vart_deriv1*vart1 + ft*( vart_deriv21*(2*R1-2*R0^2/n/(n-1)) + (4*R1+4*R2-4*R0^2/n)*(vart_deriv22+vart_deriv23-2*r*(n-2*t))/n/n )
  
  res = (2*numerator_deriv - vart_deriv)/2/vart
  
  return(res)
}


rhoW_2 = function(n, t, r, R0,R1,R2) {
 R3 = R0^2 - 2*R1 - 4*R2
 temp=r/n^3/(n-1)/(n-2)/(n-3)

  r1 = (r^2/n^3/(n-1)/(t-1))
  -(r/n^3/(n-1)/(t-1))*((2-2*n)*t+(2*n-1)*t-n+1)/(n-t-1)^2
  +(n-t)/n^3/(n-1)/(n-t-1)^2 
  
  r2_constant=1/n^3/(n-1)/(n-2)
  
  r2 = r^2*(t-2)*r2_constant/(t-1)
  - r*r2_constant/(t-1) * ((t-2)*t^2+((2-2*n)*t+4*n-4)*t+t^2+(n^2-4*n+2)*t-n^2+3*n-2)/(n-t-1)^2
  -(n-t)*r2_constant/(n-t-1)^2
  
  r3= temp*r*(t-2)*(t-3)/(t-1)
      +(n-t)*temp
      +1/(t-1)*temp*(3*t^4+(4-8*n)*t^3+(-t^2+5*t+7*n^2-5*n-7)*t^2+((2*n-2)*t^2+10*(1-n)*t-2*n^3+16*n-14)*t+(-n^2+2*n+1)*t^2+(5*n^2-14*n+7)*t+n^3-6*n^2+11*n-6)/(n-t-1)^2
      +temp/(t-1)*(t-t^2+(n-t)*(2*t-1))
      -(n-t)*temp/r*(t^2+(2-2*n)*t+n^2-2*n-1)/(n-t-1)^2
  
  r0=(r^2*t+r*(n-t)-r*t-(n-t))/n^4/(n-1)^2 
  
  numerator_deriv = 2*R1*r1 + 4*R2*r2 + R3*r3 - R0^2*r0
  
  #c
  p1_constant=1/n^3/(n-1)
  p2_constant=p1_constant/(n-2)
  p1=p1_constant*(r^2*t/(t-1)+(n-t)/(n-t-1))
  p2=p2_constant*(r^2*t*(t-2)/(t-1)+(n-t)*(n-t-2)/(n-t-1))
  p3=temp*(r*t*(t-2)*(t-3)/(t-1) +(n-t)*(n-t-2)*(n-t-3)/(n-t-1)/r +2*t*(n-t))
  p4=(r*t/n+(n-t)/n)^2/n^2/(n-1)^2
  vart=2*R1*p1+4*R2*p2+R3*p3-p4*R0^2
  
  var_r1=r^2*p1_constant*-1/(t-1)^2+p1_constant/(n-t-1)^2
  var_r2=r^2*p2_constant*(t^2-2*t+2)/(t-1)^2
  +p2_constant*-(t^2+(2-2*n)*t+n^2-2*n+2)/(n-t-1)^2
  var_r3=r*temp*2*(t^3-4*t^2+5*t-3)/(t-1)^2
  +temp/r*(2*(t^3+(4-3*n)*t^2+(3*n^2-8*n+5)*t-n^3+4*n^2-5*n+3))/(n-t-1)^2
  +2*(n-2*t)*temp
  var_r0=2*((r*t+n-t)/n)*(r-1)/n/n^2/(n-1)^2
  
  vart_deriv = 2*R1*var_r1+4*R2*var_r2+R3*var_r3-R0^2*var_r0
  res = (2*numerator_deriv - vart_deriv)/2/vart
  
  return(res)
}



# the Nu function
Nu = function(x){
  y = x/2
  (1/y)*(pnorm(y)-0.5)/(y*pnorm(y) + dnorm(y))
}

# p value approximation for single change-point
pval1 = function(n, K1, K2,scanZ, r1, r2, skew.corr=FALSE, lower=ceiling(0.05*n), upper=floor(0.95*n)) {
  output = list()
  
  if(lower<2){
    lower = 2
    #print(lower)
  }
  if(upper>(n-2)){
    upper = n-2
    #print(upper)
  }
  
  t = lower:upper
  t = as.numeric(t)
  
  R0_1 = sum(K1)
  R1_1 = sum(K1^2)
  R2_1 = sum(rowSums(K1)^2) - R1_1
  R3_1 = R0_1^2 - 2*R1_1 - 4*R2_1
  
  
  R0_2 = sum(K2)
  R1_2 = sum(K2^2)
  R2_2 = sum(rowSums(K2)^2) - R1_2
  R3_2 = R0_2^2 - 2*R1_2 - 4*R2_2
  
  R1_cross=sum(K1*K2)
  R2_cross=sum(rowSums(K1)*rowSums(K2)) - R1_cross
  R3_cross=R0_1*R0_2-2*R1_cross-4*R2_cross
  
  #weight a
  m1=(n-2)*R1_1+(2*R1_1+4*R2_1+R3_1)/(n-1)-2*(R1_1+R2_1)
  m2=(n-2)*R1_2+(2*R1_2+4*R2_2+R3_2)/(n-1)-2*(R1_2+R2_2)
  m_cross=(n-2)*R1_cross+(2*R1_cross+4*R2_cross+R3_cross)/(n-1)-2*(R1_cross+R2_cross)
  a = (m2-m_cross)/(m1-m_cross)
  
  
  if (skew.corr==FALSE) {
    bD1 = scanZ$ZD1$Zmax
    if (bD1>0) {
      integrandD1 = function(t){
        c1 = rhoD(n, t)
        c1*Nu(sqrt(2*bD1^2*c1))
      }
      pval.ZD1 = 2*dnorm(bD1)*bD1*integrate(integrandD1, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value
    } else {
      pval.ZD1 = 1
    }
    output$Z_D1 = min(pval.ZD1,1)
    output$tauhat[1]=scanZ$ZD1$tauhat
    
    
    bW1_r1 = scanZ$ZW1_r1$Zmax
    if (bW1_r1>0) {
      integrandW1_r1 = function(t){
        c1 = rhoW(n, t, r1, R0_1, R1_1, R2_1)
        c1*Nu(sqrt(2*bW1_r1^2*c1))
      }
      
      pval.ZW1_r1 = dnorm(bW1_r1)*bW1_r1*integrate(integrandW1_r1, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value
    } else {
      pval.ZW1_r1 = 1
    }
    output$Z_W1_r1 = min(pval.ZW1_r1,1)
    output$tauhat[2] = scanZ$ZW1_r1$tauhat
    
    bW1_r2 = scanZ$ZW1_r2$Zmax
    if (bW1_r2>0) {
      integrandW1_r2 = function(t){
        c1 = rhoW(n, t, r2, R0_1, R1_1, R2_1)
        c1*Nu(sqrt(2*bW1_r2^2*c1))
      }
      pval.ZW1_r2 = 
        dnorm(bW1_r2)*bW1_r2*integrate(integrandW1_r2, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value}
  else {
      pval.ZW1_r2 = 1
    }
    output$ZW1_r2 = min(pval.ZW1_r2,1)
    output$tauhat[3]=scanZ$ZW1_r2$tauhat
    
    #K2
    #D2
    bD2 = scanZ$ZD2$Zmax
    if (bD2>0) {
      integrandD2 = function(t){
        c1 = rhoD(n, t)
        c1*Nu(sqrt(2*bD2^2*c1))
      }
      pval.ZD2 = 2*dnorm(bD2)*bD2*integrate(integrandD2, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value
    } else {
      pval.ZD2 = 1
    }
    output$ZD2 = min(pval.ZD2,1)
    output$tauhat[4]=scanZ$ZD2$tauhat
    
    #W2_r1
    bW2_r1 = scanZ$ZW2_r1$Zmax
    if (bW2_r1>0) {
      integrandW2_r1 = function(t){
        c1 = rhoW(n, t, r1, R0_2, R1_2, R2_2)
        c1*Nu(sqrt(2*bW2_r1^2*c1))
      }
      pval.ZW2_r1 = dnorm(bW2_r1)*bW2_r1*integrate(integrandW2_r1, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value
    } else {
      pval.ZW2_r1 = 1
    }
    output$ZW2_r1 = min(pval.ZW2_r1,1)
    output$tauhat[5]=scanZ$ZW2_r1$tauhat
    
    #W2_r2
    bW2_r2 = scanZ$ZW2_r2$Zmax
    if (bW2_r2>0) {
      integrandW2_r2 = function(t){
        c1 = rhoW(n, t, r2, R0_2, R1_2, R2_2)
        c1*Nu(sqrt(2*bW2_r2^2*c1))
      }
      pval.ZW2_r2 = 
        dnorm(bW2_r2)*bW2_r2*integrate(integrandW2_r2, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value
        
    } else {
      pval.ZW2_r2 = 1
    }
    output$ZW2_r2 = min(pval.ZW2_r2,1)
    output$tauhat[6]=scanZ$ZW2_r2$tauhat
    
    
    
    #3min(max(Z_D_diff,Z_D_sum),max(Z_Wr1_diff,Z_Wr1_sum),max(Z_Wr2_diff,Z_Wr2_sum))
    #b_Dmax = max(scanZ$D_diff$max,scanZ$D_sum$max)
    #if (b_Dmax>0) {
      #integrandD_max = function(t){
        #c1 = rhoD(n, t)
        #c1*Nu(sqrt(2*b_Dmax^2*c1))
      #}
     # pval.ZD_max = 2*dnorm(b_Dmax)*b_Dmax*integrate(integrandD_max, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value
    #} else {
     # pval.ZD_max = 1
    #}
    
    #p.ZD_max = min(pval.ZD_max,1)
 
    #output$pmax.D=1-(1-min(p.ZD_max,1))*(1-min(p.ZD_max,1))
    
    
    #bW_max_r1 = max(scanZ$W_diff_r1$max,scanZ$W_sum_r1$max)
    #if (bW_max_r1>0) {
     # integrandW_diff_r1 = function(t){
       # c1 = rhoW_2(n, t, r1, R1_1+R1_2-2*R1_cross, R2_1+R2_2-2*R2_cross,R3_1+R3_2-2*R3_cross,R0_1^2+R0_2^2-2*R0_1*R0_2)
        #c1*Nu(sqrt(2*bW_max_r1^2*c1))
      #}
      
      #pval.ZW_diff_r1 = tryCatch(dnorm(bW_max_r1)*bW_max_r1*integrate(integrandW_diff_r1, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value,error=function(e){1}
      #)} else {
        #pval.ZW_diff_r1 = 1
      #}
    #p.ZW_diff_r1 = min(pval.ZW_diff_r1,1)
    
    #if (bW_max_r1>0) {
      #integrandW_sum_r1 = function(t){
       # c1 = rhoW_2(n, t, r1, a^2*R1_1+R1_2-2*a*R1_cross, a^2*R2_1+R2_2-2*a*R2_cross,a^2*R3_1+R3_2-2*a*R3_cross,a^2*R0_1^2+R0_2^2-2*a*R0_1*R0_2)
       # c1*Nu(sqrt(2*bW_max_r1^2*c1))
     # }
      
     # pval.ZW_sum_r1 = tryCatch(dnorm(bW_max_r1)*bW_max_r1*integrate(integrandW_sum_r1, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value,error=function(e){1}
     # )} else {
     #   pval.ZW_sum_r1 = 1
     # }
    #p.ZW_sum_r1 = min(pval.ZW_sum_r1,1)
    
    #output$pmax.W_r1=1-(1-p.ZW_sum_r1)*(1-p.ZW_diff_r1)
    
    
    
   
    
    #bW_max_r2 = max(scanZ$W_diff_r2$max,scanZ$W_sum_r2$max)
    #if (bW_max_r2>0) {
    #  integrandW_diff_r2 = function(t){
    #    c1 = rhoW_2(n, t, r2, R1_1+R1_2-2*R1_cross, R2_1+R2_2-2*R2_cross,R3_1+R3_2-2*R3_cross,R0_1^2+R0_2^2-2*R0_1*R0_2)
    #    c1*Nu(sqrt(2*bW_max_r2^2*c1))
    #  }
      
    #  pval.ZW_diff_r2 = tryCatch(dnorm(bW_max_r2)*bW_max_r2*integrate(integrandW_diff_r2, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value,error=function(e){1}
   # )} else {
    #  pval.ZW_diff_r2 = 1
   # }
   # p.ZW_diff_r2 = min(pval.ZW_diff_r2,1)
    
    #if (bW_max_r2>0) {
    #  integrandW_sum_r2 = function(t){
    #    c1 = rhoW_2(n, t, r2, a^2*R1_1+R1_2-2*a*R1_cross, a^2*R2_1+R2_2-2*a*R2_cross,a^2*R3_1+R3_2-2*a*R3_cross,a^2*R0_1^2+R0_2^2-2*a*R0_1*R0_2)
    #    c1*Nu(sqrt(2*bW_max_r2^2*c1))
    #  }
      
    #  pval.ZW_sum_r2 = tryCatch(dnorm(bW_max_r2)*bW_max_r2*integrate(integrandW_sum_r2, lower, upper, subdivisions=3000, stop.on.error=FALSE)$value,error=function(e){1}
    #  )} else {
     #   pval.ZW_sum_r2 = 1
     # }
    #p.ZW_sum_r2 = min(pval.ZW_sum_r2,1)
  
    #output$pmax.W_r2=1-(1-p.ZW_sum_r2)*(1-p.ZW_diff_r2)
    
    return(output)
  }
  
  
}

#permutation p-value for 1 kernel
permpval1 = function(n, K, scanZ, r1, r2, B=100, n0=ceiling(0.05*n), n1=floor(0.95*n)) {
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  Z.D = Z.W1 = Z.W2 = gkcp = matrix(0,B,n)
  
  for(b in 1:B) {
    if(b%%1000 ==0) {
      message(b, "permutations completed.\n")
    }
    id0 = sample(1:n, replace = FALSE)    # permute the data
    
    K_id = K[id0, id0]
    gcpstar = computeSTAT1(n, K_id, r1, r2, n0, n1)
    
    Z.D[b,] = gcpstar$Z_D$seq
    Z.W1[b,] = gcpstar$Z_W1$seq
    Z.W2[b,] = gcpstar$Z_W2$seq
    gkcp[b,] = gcpstar$GKCP$seq
  }
  
  output = list()
  p=1-(0:(B-1))/B
  
  maxZ_D = apply(Z.D[,n0:n1],1,max)
  maxZs_D = sort(maxZ_D)
  ZD.pval.perm = min(1, 2*length(which(maxZs_D>=scanZ$Z_D$Zmax))/B )
  output$Z_D = list(pval=ZD.pval.perm, curve=cbind(maxZs_D,p), maxZs_D=maxZs_D, Z=Z.D)
  
  maxZ_W1 = apply(Z.W1[,n0:n1],1,max)
  maxZs_W1 = sort(maxZ_W1)
  ZW1.pval.perm = min(1, length(which(maxZs_W1>=scanZ$Z_W1$Zmax))/B )
  output$Z_W1 = list(pval=ZW1.pval.perm, curve=cbind(maxZs_W1,p), maxZs_W1=maxZs_W1, Z=Z.W1)
  
  maxZ_W2 = apply(Z.W2[,n0:n1],1,max)
  maxZs_W2 = sort(maxZ_W2)
  ZW2.pval.perm = min(1, length(which(maxZs_W2>=scanZ$Z_W2$Zmax))/B )
  output$Z_W2 = list(pval=ZW2.pval.perm, curve=cbind(maxZs_W2,p), maxZs_W2=maxZs_W2, Z=Z.W2)
  
  maxZ_D = apply(gkcp[,n0:n1],1,max)
  maxZs_D = sort(maxZ_D)
  GKCP.pval.perm = min(1, length(which(maxZs_D>=scanZ$GKCP$Zmax))/B )
  output$GKCP = list(pval=GKCP.pval.perm, curve=cbind(maxZs_D,p), maxZs_D=maxZs_D, Z=gkcp)
  
  return(output)
}

#for 2 kernel

permpval2 = function(n, K1, K2, r1=0.5, r2=2, B=100, n0=ceiling(0.05*n), n1=floor(0.95*n)) {
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  Z.D1 =Z.D2= Z.W1_r1 = Z.W1_r2 =  Z.W2_r1 =Z.W2_r2=gkcp = matrix(0,B,n)
  scanZ=calculate_statistic_new(K1,K2,n)
  for(b in 1:B) {
    if(b%%1000 ==0) {
      message(b, "permutations completed.\n")
    }
    id0 = sample(1:n, replace = FALSE)    # permute the data
    
    K1_id = K1[id0, id0]
    K2_id = K2[id0, id0]
    gcpstar = calculate_statistic_new(K1_id,K2_id,n)
    #Z_s = calculate_statistic_new_separate(K1_id,K2_id,r1,r2,n)
    
    #Z.D1[b,] = Z_s$ZD1$scan
    #Z.D2[b,] = Z_s$ZD2$scan
    #Z.W1_r1[b,] = Z_s$ZW1_r1$scan
    #Z.W1_r2[b,] = Z_s$ZW1_r2$scan
    #Z.W2_r1[b,] = Z_s$ZW2_r1$scan
    #Z.W2_r2[b,] = Z_s$ZW2_r2$scan
    gkcp[b,] = gcpstar$GKCP
  }
  
  output = list()
  p=1-(0:(B-1))/B
  
  
  max_GKCP = apply(gkcp[,n0:n1],1,max)
  max_GKCPS = sort(max_GKCP)
  GKCP.pval.perm = min(1, length(which(max_GKCPS>=max(scanZ$GKCP[n0:n1])))/B)
  output$GKCP = list(pval=GKCP.pval.perm, curve=cbind(max_GKCPS,p),max_GKCPS=max_GKCPS, Z=gkcp)
  
  return(output)
}



permpval_max = function(n, K1, K2, r1=0.5, r2=2, B=100, n0=ceiling(0.05*n), n1=floor(0.95*n)) {
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  Z.D1 =Z.D2= Z.W1  =Z.W2=gkcp = matrix(0,B,n)
  scanZ=calculate_statistic_new(K1,K2,n)
  for(b in 1:B) {
    if(b%%1000 ==0) {
      message(b, "permutations completed.\n")
    }
    id0 = sample(1:n, replace = FALSE)    # permute the data
    
    K1_id = K1[id0, id0]
    K2_id = K2[id0, id0]
    #gcpstar = calculate_statistic_new(K1_id,K2_id,n)
   
    Z.D1[b,] = gcpstar$ZD1
    Z.D2[b,] = gcpstar$ZD2
    Z.W1[b,] = gcpstar$ZW1
    Z.W2[b,] = gcpstar$ZW2
    #gkcp[b,] = gcpstar$GKCP
  }
  
  output = list()
  p=1-(0:(B-1))/B
  
  
  max_ZD1 = apply(abs(Z.D1[,n0:n1]),1,max)
  max_ZD1S = sort(max_ZD1)
  
  max_ZD2 = apply(abs(Z.D2[,n0:n1]),1,max)
  max_ZD2S = sort(max_ZD2)
  
  max_ZW1 = apply(abs(Z.W1[,n0:n1]),1,max)
  max_ZW1S = sort(max_ZW1)
  
  max_ZW2 = apply(abs(Z.W2[,n0:n1]),1,max)
  max_ZW2S = sort(max_ZW2)
  
  #GKCP.pval.perm = min(1, length(which(max_GKCPS>=max(scanZ$GKCP[n0:n1])))/B)
  #output$GKCP = list(pval=GKCP.pval.perm, curve=cbind(max_GKCPS,p),max_GKCPS=max_GKCPS, Z=gkcp)
  
  ZD1.pval.perm = min(1, length(which(max_ZD1S>=max(scanZ$ZD1[n0:n1])))/B)
  output$ZD1 = list(pval=ZD1.pval.perm, curve=cbind(max_ZD1S,p),max_GKCPS=max_ZD1S, Z=Z.D1)
  
  ZD2.pval.perm = min(1, length(which(max_ZD2S>=max(scanZ$ZD2[n0:n1])))/B)
  output$ZD2 = list(pval=ZD2.pval.perm, curve=cbind(max_ZD2S,p),max_GKCPS=max_ZD2S, Z=Z.D2)
  
  ZW1.pval.perm = min(1, length(which(max_ZW1S>=max(scanZ$ZW1[n0:n1])))/B)
  output$ZW1 = list(pval=ZW1.pval.perm, curve=cbind(max_ZW1S,p),max_GKCPS=max_ZW1S, Z=Z.W1)
  
  ZW2.pval.perm = min(1, length(which(max_ZW2S>=max(scanZ$ZW2[n0:n1])))/B)
  output$ZW2 = list(pval=ZW2.pval.perm, curve=cbind(max_ZW2S,p),max_GKCPS=max_ZW2S, Z=Z.W2)
  
  return(output)
}

kernel_two_sample_gaussian<-function(K1,n1,n2){
  if(n0<2){
    n0=2
  }
  if(n1>(n-2)){
    n1=n-2
  }
  
  t = n1
  R_temp1 = rowSums(K1)
  #R_temp2 = rowSums(K2)
  
  K1x = K1y = rep(0, n)
  K1x[2] = sum(K1[1:2,1:2])
  K1y[2] = sum(K1[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col = K1[,i]
    add = sum(temp_col[1:i])
    subtract = R_temp1[i] - add
    K1x[i] = (K1x[i-1] + 2*add)
    K1y[i] = (K1y[i-1] - 2*subtract)
  }
  
  K1x=K1x/(t*(t-1))
  K1y=K1y/((n-t)*(n-t-1))
  
  
  K2x = K2y = rep(0, n)
  K2x[2] = sum(K2[1:2,1:2])
  K2y[2] = sum(K2[3:n,3:n])
  for (i in 3:(n-2)) {
    temp_col2 = K2[,i]
    add = sum(temp_col2[1:i])
    subtract = R_temp2[i] - add
    K2x[i] = (K2x[i-1] + 2*add)
    K2y[i] = (K2y[i-1] - 2*subtract)
  }
  
  K2x=K2x/(t*(t-1))
  K2y=K2y/((n-t)*(n-t-1))
  
  R0_1 = sum(K1)
  mu_K1x = R0_1/n/(n-1)
  mu_K1y = R0_1/n/(n-1)
  
  R0_2 = sum(K2)
  mu_K2x = R0_2/n/(n-1)
  mu_K2y = R0_2/n/(n-1)
  
  A_2 = sum(K2^2)
  B_2 = sum(R_temp2^2) - A_2
  C_2 = R0_2^2 - 2*A_2 - 4*B_2
  
  A_1 = sum(K1^2)
  B_1 = sum(R_temp1^2) - A_1
  C_1 = R0_1^2 - 2*A_1 - 4*B_1
  
  A_cross=sum(K1*K2)
  B_cross=sum(R_temp2*R_temp1) - A_cross
  C_cross=R0_1*R0_2-2*A_cross-4*B_cross
  
  p1 = t*(t-1)/n/(n-1)
  p2 = p1*(t-2)/(n-2)
  p3 = p2*(t-3)/(n-3)
  
  q1 = (n-t)*(n-t-1)/n/(n-1)
  q2 = q1*(n-t-2)/(n-2)
  q3 = q2*(n-t-3)/(n-3)
  
  var_K1x = (2*A_1*p1 + 4*B_1*p2 + C_1*p3)/t/t/(t-1)/(t-1) - mu_K1x^2
  var_K1y = (2*A_1*q1 + 4*B_1*q2 + C_1*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y^2
  cov_K1x_K1y = C_1/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K1y
  
  var_K2x = (2*A_2*p1 + 4*B_2*p2 + C_2*p3)/t/t/(t-1)/(t-1) - mu_K2x^2
  var_K2y = (2*A_2*q1 + 4*B_2*q2 + C_2*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K2y^2
  cov_K2x_K2y = C_2/n/(n-1)/(n-2)/(n-3) - mu_K2x*mu_K2y
  
  cov_K1x_K2x=(2*A_cross*p1 + 4*B_cross*p2 + C_cross*p3)/t/t/(t-1)/(t-1) - mu_K2x*mu_K1x
  cov_K1y_K2y=(2*A_cross*q1 + 4*B_cross*q2 + C_cross*q3)/(n-t)/(n-t)/(n-t-1)/(n-t-1) - mu_K1y*mu_K2y
  cov_K1x_K2y=cov_K1y_K2x=C_cross/n/(n-1)/(n-2)/(n-3) - mu_K1x*mu_K2y
  
  # test statistic D1
  D.weight1 = t*(t-1)/(n*(n-1))
  D.weight2 = -(n-t)*(n-t-1)/(n*(n-1))
  
  mean.D1 = mu_K1x*D.weight1 + mu_K1y*D.weight2
  var.D1 = (D.weight1^2)*var_K1x + (D.weight2^2)*var_K1y + 2*D.weight1*D.weight2*cov_K1x_K1y
  D1=K1x*D.weight1 + K1y*D.weight2
  
  # test statistic W1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1 = mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1 = var_K1x*w.weight1^2 + var_K1y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K1x_K1y
  W1 = K1x*w.weight1 + K1y*w.weight2
  
  
  # test statistic W1_r1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1_r1 = r1*mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1_r1 = var_K1x*w.weight1^2*r1^2 + var_K1y*w.weight2^2 + 2*r1*w.weight1*w.weight2*cov_K1x_K1y
  W1_r1 = K1x*w.weight1*r1 + K1y*w.weight2
  
  # test statistic W1_r2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  mean.W1_r2 = r2*mu_K1x*w.weight1 + mu_K1y*w.weight2
  var.W1_r2 = var_K1x*w.weight1^2*r2^2 + var_K1y*w.weight2^2 + 2*r2*w.weight1*w.weight2*cov_K1x_K1y
  W1_r2 = K1x*w.weight1*r2 + K1y*w.weight2
  
  # test statistic D2
  mean.D2 = mu_K2x*D.weight1 + mu_K2y*D.weight2
  var.D2 = (D.weight1^2)*var_K2x + (D.weight2^2)*var_K2y + 2*D.weight1*D.weight2*cov_K2x_K2y
  D2 = K2x*D.weight1 + K2y*D.weight2
  
  
  # test statistic W2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2 = mu_K2x*w.weight1 + mu_K2y*w.weight2
  var.W2 = var_K2x*w.weight1^2 + var_K2y*w.weight2^2 + 2*w.weight1*w.weight2*cov_K2x_K2y
  W2 = K2x*w.weight1 + K2y*w.weight2
  
  # test statistic W2_r1
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2_r1 = r1*mu_K2x*w.weight1 + mu_K2y*w.weight2
  var.W2_r1 = var_K2x*w.weight1^2*r1^2 + var_K2y*w.weight2^2 + 2*r1*w.weight1*w.weight2*cov_K2x_K2y
  W2_r1 = r1*K2x*w.weight1 + K2y*w.weight2
  
  # test statistic W2_r2
  w.weight1 = t/n
  w.weight2 = (n-t)/n
  
  mean.W2_r2 = mu_K2x*w.weight1*r2 + mu_K2y*w.weight2
  var.W2_r2 = var_K2x*w.weight1^2*r2^2 + var_K2y*w.weight2^2 + 2*r2*w.weight1*w.weight2*cov_K2x_K2y
  W2_r2 = K2x*w.weight1*r2 + K2y*w.weight2
  
  cov_w1_w2 <- w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*w.weight1*w.weight2*cov_K1x_K2y
  cov_D1_D2 <- D.weight1^2*cov_K1x_K2x + D.weight2^2*cov_K1y_K2y + 2*D.weight1*D.weight2*cov_K1x_K2y
  
  cov_w1_w2_r1 <- r1^2*w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*r1*w.weight1*w.weight2*cov_K1x_K2y
  cov_w1_w2_r2 <- r2^2*w.weight1^2*cov_K1x_K2x + w.weight2^2*cov_K1y_K2y+ 2*r2*w.weight1*w.weight2*cov_K1x_K2y
  
  #weight x (D)
  t2=(A_2+B_2)-(2*A_2+4*B_2+C_2)/n
  t1=(A_1+B_1)-(2*A_1+4*B_1+C_1)/n
  t_cross=(A_cross+B_cross)-(2*A_cross+4*B_cross+C_cross)/n
  x = (t2-t_cross)/(t1-t_cross)
  
  #weight a (W)
  m1=(n-2)*A_1+(2*A_1+4*B_1+C_1)/(n-1)-2*(A_1+B_1)
  m2=(n-2)*A_2+(2*A_2+4*B_2+C_2)/(n-1)-2*(A_2+B_2)
  m_cross=(n-2)*A_cross+(2*A_cross+4*B_cross+C_cross)/(n-1)-2*(A_cross+B_cross)
  a = (m2-m_cross)/(m1-m_cross)
  
  #Standardized W1_r1
  ZW1_r1= (W1_r1-mean.W1_r1)/sqrt(var.W1_r1)
  #Standardized W1_r2
  ZW1_r2= (W1_r2-mean.W1_r2)/sqrt(var.W1_r2)
  #Standardized W1
  ZW1= (W1-mean.W1)/sqrt(var.W1)
  #Standardized D1
  ZD1=(D1-mean.D1)/sqrt(var.D1)
  #Standardized W2_r1
  ZW2_r1= (W2_r1-mean.W2_r1)/sqrt(var.W2_r1)
  #Standardized W2_r2
  ZW2_r2= (W2_r2-mean.W2_r2)/sqrt(var.W2_r2)
  #Standardized W2
  ZW2= (W2-mean.W2)/sqrt(var.W2)
  #Standardized D2
  ZD2=(D2-mean.D2)/sqrt(var.D2)
  
  scanZ=list()
  scanZ$ZW1_r1$scan=ZW1_r1
  scanZ$ZW1_r1$Zmax=max(ZW1_r1[n0:n1])
  scanZ$ZW1_r1$tauhat=temp[which.max(ZW1_r1[n0:n1])]
  
  scanZ$ZW1_r2$scan=ZW1_r2
  scanZ$ZW1_r2$Zmax=max(ZW1_r2[n0:n1])
  scanZ$ZW1_r2$tauhat=temp[which.max(ZW1_r2[n0:n1])]
  
  scanZ$ZW1$scan=ZW1
  scanZ$ZW1$Zmax=max(ZW1[n0:n1])
  scanZ$ZW1$tauhat=temp[which.max(ZW1[n0:n1])]
  
  scanZ$ZD1$scan=ZD1
  scanZ$ZD1$Zmax=max(abs(ZD1[n0:n1]))
  scanZ$ZD1$tauhat=temp[which.max(abs(ZD1[n0:n1]))]
  
  scanZ$ZW2_r1$scan=ZW2_r1
  scanZ$ZW2_r1$Zmax=max(ZW2_r1[n0:n1])
  scanZ$ZW2_r1$tauhat=temp[which.max(ZW2_r1[n0:n1])]
  
  scanZ$ZW2_r2$scan=ZW2_r2
  scanZ$ZW2_r2$Zmax=max(ZW2_r2[n0:n1])
  scanZ$ZW2_r2$tauhat=temp[which.max(ZW2_r2[n0:n1])]
  
  scanZ$ZW2$scan=ZW2
  scanZ$ZW2$Zmax=max(ZW2[n0:n1])
  scanZ$ZW2$tauhat=temp[which.max(ZW2[n0:n1])]
  
  scanZ$ZD2$scan=ZD2
  scanZ$ZD2$Zmax=max(abs(ZD2[n0:n1]))
  scanZ$ZD2$tauhat=temp[which.max(abs(ZD2[n0:n1]))]
  
  scanZ$weightW=a
  scanZ$weightD=x
  
  #Standardized W1-W2
  Diff_W=(W1-W2-mean.W1+mean.W2)/sqrt(var.W1+var.W2-2*cov_w1_w2)
  
  #Standardized D1-D2
  Diff_D=(D1-D2-mean.D1+mean.D2)/sqrt(var.D1+var.D2-2*cov_D1_D2)
  
  #Standardized aW1+W2
  Sum_W=(a*W1+W2-a*mean.W1-mean.W2)/sqrt(a^2*var.W1+var.W2+2*a*cov_w1_w2)
  
  #Standardized xD1+D2
  Sum_D=(x*D1+D2-x*mean.D1-mean.D2)/sqrt(x^2*var.D1+var.D2+2*x*cov_D1_D2)
  
  #weighted sum of D1  and D2
  scanZ$D_sum$scan=Sum_D
  scanZ$D_sum$max=max(abs(Sum_D[n0:n1]))
  scanZ$D_sum$tauhat=temp[which.max(abs(Sum_D[n0:n1]))]
  
  #difference of D1 and D2
  scanZ$D_diff$scan=Diff_D
  scanZ$D_diff$max=max(abs(Diff_D)[n0:n1])
  scanZ$D_diff$tauhat=temp[which.max(abs(Diff_D)[n0:n1])]
  
  #diff of W1  and W2 
  scanZ$W_diff$scan=Diff_W
  scanZ$W_diff$max=max(abs(Diff_W)[n0:n1])
  scanZ$W_diff$tauhat=temp[which.max(abs(Diff_W)[n0:n1])]
  
  #weighted sum of W1  and W2 
  scanZ$W_sum$scan=Sum_W
  scanZ$W_sum$max=max(Sum_W[n0:n1])
  scanZ$W_sum$tauhat=temp[which.max((Sum_W)[n0:n1])]
  
  #GKCP
  scanZ$GKCP$scan=Sum_W^2+Sum_D^2+Diff_W^2+Diff_D^2
  scanZ$GKCP$max=max((Sum_W^2+Sum_D^2+Diff_W^2+Diff_D^2)[n0:n1])
  scanZ$GKCP$tauhat=temp[which.max((Sum_W^2+Sum_D^2+Diff_W^2+Diff_D^2)[n0:n1])]
  
  #added for debugging
  scanZ$W1$scan=W1-mean.W1
  scanZ$W2$scan=W2-mean.W2
  scanZ$D1$scan=D1-mean.D1
  scanZ$D2$scan=D2-mean.D2
  scanZ$W_diff0$scan=W1-W2-mean.W1+mean.W2
  scanZ$D_diff0$scan=D1-D2-mean.D1+mean.D2
  
  scanZ$W_sum0$scan=a*W1+W2-a*mean.W1-mean.W2
  scanZ$D_sum0$scan=x*D1+D2-x*mean.D1-mean.D2
  #
  
  #third_moment_K1= DW_third_moment(n,K1,r1=r1,r2=r2)
  #third_moment_K2= DW_third_moment(n,K2,r1=r1,r2=r2)
  
  #skewness of Z_D1
  #ZD1.3=(third_moment_K1$ED.3-3*mean.D1*var.D1-(mean.D1^3))/sqrt(var.D1)^3
  #scanZ$ZD1$skewness=ZD1.3
  
  #skewness of Z_D2
  #ZD2.3=(third_moment_K2$ED.3-3*mean.D2*var.D2-(mean.D2^3))/sqrt(var.D2)^3
  #scanZ$ZD2$skewness=ZD2.3
  
  #skewness of Z_w1_r1
  #ZW1_r1.3=(third_moment_K1$EW1.3-3*mean.W1_r1*var.W1_r1-(mean.W1_r1^3))/sqrt(var.W1_r1)^3
  #scanZ$ZW1_r1$skewness=ZW1_r1.3
  #skewness of Z_w2_r1
  #ZW2_r1.3=(third_moment_K2$EW1.3-3*mean.W2_r1*var.W2_r1-(mean.W2_r1^3))/sqrt(var.W2_r1)^3
  #scanZ$ZW2_r1$skewness=ZW2_r1.3
  #skewness of Z_w1_r2
  #ZW1_r2.3=(third_moment_K1$EW2.3-3*mean.W1_r2*var.W1_r2-(mean.W1_r2^3))/sqrt(var.W1_r2)^3
  #scanZ$ZW1_r2$skewness=ZW1_r2.3
  #skewness of Z_w2_r2
  #ZW2_r2.3=(third_moment_K2$EW2.3-3*mean.W2_r2*var.W2_r2-(mean.W2_r2^3))/sqrt(var.W2_r2)^3
  #scanZ$ZW2_r2$skewness=ZW2_r2.3
  return(scanZ)
}

