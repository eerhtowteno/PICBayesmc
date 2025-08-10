###############################################################################
#  estimation procedures
# ###############################################################################
#data: including the observations
# X, V: linear and nonlinear covariates in the latency components
# Z, W: linear and nonlinear covariates in the incidence components
# L, R: left and right endpoints of intervals
# y: status for the observations
# vknots,V.df, V.order: number of knots, degree of freedom for the nonlinear function phi(v)
# Vgrid: evaluation points for the phi(v)
# wknots, W.df, W.order:number of knots, degree of freedom for the nonlinear function g(w)
# Wgrid: evaluation points for the g(w)
# a_eta, b_eta: hyperparameters
# sig_beta, sig_alpha, sig_rho, sig_theta: variance of prior distribution
# coef_range_beta, coef_range_alpha, coef_range_rho, coef_range_theta: the range of coefficients

rm(list=ls())
library(dlm)
library(splines)
library(icenReg)
library(survival)
library(dplyr)
bmc_est <- function (data,order, knots, df,grids,
                 V.order,Vknots,V.df,Vgrid, 
                 W.order,Wknots,W.df,Wgrid,
                 a_eta, b_eta,
                 coef_range_beta,sig_beta,
                 coef_range_alpha,sig_alpha,
                 coef_range_rho,sig_rho,
                 coef_range_theta,sig_theta,total,
                 burnin, thin) 
{
  #main function
  Z = cbind(data$Z.1,data$Z.2) 
  W = data$W 
  X = cbind(data$X.1,data$X.2) 
  V = data$V
  L = data$L 
  R = data$R
  y = data$y
  L=as.matrix(L,ncol=1)
  R=as.matrix(R,ncol=1)
  R2=ifelse(is.finite(R),R,0)
  xcov=as.matrix(X)
  zcov= as.matrix(Z)
  wcov = as.matrix(W)
  vcov = as.matrix(V)
  p=ncol(xcov)
  q= ncol(zcov)
  
  n1 = sum(y == 3)
  n2 = sum(y != 3)
  N = n1 + n2
  t <- rep(0, N)
  
  if (is.null(knots)) {knots<-seq(min(c(L,R2)),max(c(L,R2))+1,length=df)}
  # basis function for f(v)
  if (is.null(Vknots)) {
    Vknots = quantile(V,seq(0,1,length.out=V.df))
    # Vknots = seq(min(V),max(V),length.out=V.df)
    # Vknots = seq(-2,2,length.out=V.df)
    Vknots = Vknots[-c(1,length(Vknots))] # inner knots
    # Vknots = c(-0.5,0,0.5)
  }
  
  # basis function for g(W)
  if (is.null(Wknots)) {
    Wknots = quantile(W,seq(0,1,length.out=W.df))
    # Wknots = seq(min(W),max(W),length.out=W.df)
    # Wknots = seq(-2,2,length.out=W.df)
    Wknots = Wknots[-c(1,length(Wknots))]
    # Wknots = c(-0.5,0,0.5)
  }
  
  for (i in 1:N) {
    t[i] = ifelse(y[i] == 3, L[i], 0)
  }
  
  K = length(knots) - 2 + order
  kgrids = length(grids)
  bmsT = Mspline(t[1:n1], order, knots)
  bisT = Ispline(t[1:n1], order, knots)
  bisL = Ispline(L[(n1 + 1):N, ], order, knots)
  bisR = Ispline(R[(n1 + 1):N, ], order, knots)
  bisg = Ispline(grids, order, knots)
  
  bsV = bs(V, knots = Vknots, degree = V.order)  # n*kv
  bsVg = bs(Vgrid,knots = Vknots, degree = V.order)
  bsW = bs(W,knots= Wknots, degree = W.order)
  bsWg =  bs(Wgrid,knots= Wknots, degree = W.order)
  kf = ncol(bsV);kfe = nrow(bsVg)
  kg = ncol(bsW); kgg = nrow(bsWg)
  
  ## initial value
  U = ifelse(y==2,0,1)
  eta = rgamma(1, a_eta, rate = b_eta)
  gamcoef = matrix(rgamma(K, 1, rate = 1), ncol = K)
  beta = matrix(rep(0, p), ncol = 1)
  
  icsp = ic_sp(Surv(L,R,type="interval2")~X.1+X.2+bs(V, knots = Vknots, degree = V.order),data=data[is.finite(data$R),])
  fprior= icsp$coefficients[c(-1,-2)]
  # fprior = rep(0,kf)
  fcoef = fprior
  rho=c(beta,fcoef)
  
  alpha = rep(0,q)
  glm_fit= glm(U~Z.1+Z.2+bs(W,knots= Wknots, degree = W.order)-1,family = binomial(),data = data)
  gprior= glm_fit$coefficients[-(1:2)]
  # gprior= rep(0,kg)
  gcoef = gprior
  theta = c(alpha,gcoef)
  u = array(rep(0, n1 * K), dim = c(n1, K))
  for (i in 1:n1) {
    u[i, ] = rmultinom(1, 1, gamcoef * t(bmsT[, i]))
  }
  lambdatT = t(gamcoef %*% bmsT)
  LambdatT = t(gamcoef %*% bisT)
  LambdatL = t(gamcoef %*% bisL)
  LambdatR = t(gamcoef %*% bisR)
  Lambdatg = t(gamcoef %*% bisg)
  parbeta = array(rep(0, total * p), dim = c(total, p))
  parfcoef = array(rep(0,total*kf),dim=c(total,kf))
  parf = array(rep(0,total*kfe),dim=c(total,kfe))
  paralpha = array(rep(0,total*q), dim= c(total, q))  
  pargcoef = array(rep(0,total*kg), dim= c(total, kg))
  parg = array(rep(0,total*kgg), dim= c(total, kgg))
  pareta = array(rep(0, total), dim = c(total, 1))
  pargam = array(rep(0, total * K), dim = c(total, K))
  parsurv0 = array(rep(0, total * kgrids), dim = c(total, kgrids))
  parlambdatT = array(rep(0, total * n1), dim = c(total, n1))
  parLambdatT = array(rep(0, total * n1), dim = c(total, n1))
  parLambdatL = array(rep(0, total * n2), dim = c(total, n2))
  parLambdatR = array(rep(0, total * n2), dim = c(total, n2))
  
  iter = 1
  while (iter < total+1) {
    z = array(rep(0, n2), dim = c(n2, 1))
    w = z
    zz = array(rep(0, n2 * K), dim = c(n2, K))
    ww = zz
    for (j in 1:n2) {
      if (y[n1+j]== 0) {
        templam1 = LambdatR[j] * exp(xcov[(n1 + j), ] %*% beta+bsV[(n1 + j), ]%*%fcoef)
        
        z[j] = positivepoissonrnd(templam1)
        zz[j, ] = rmultinom(1, z[j], gamcoef * t(bisR[, j]))
      }
      else if (y[n1+j] == 1) {
        templam1 = (LambdatR[j] - LambdatL[j]) * exp(xcov[(n1 + j), ]%*%beta+bsV[(n1 + j), ]%*%fcoef)
        
        w[j] = positivepoissonrnd(templam1)
        ww[j, ] = rmultinom(1, w[j], gamcoef * t(bisR[, j] - bisL[, j]))
      }
    }
    te1 = z * (y[(n1 + 1):N] == 0) + w * (y[(n1 + 1):N] == 1)
    te2 = LambdatR * (y[(n1 + 1):N] == 0) + LambdatR * (y[(n1 + 1):N] == 1) + LambdatL * (y[(n1 + 1):N] == 2)*U[(n1+1):N]
    te3 = LambdatT
    
    ##sample gamma
    for (l in 1:K) {
      tempa = 1 + sum(u[, l]) + sum(zz[, l] * (y[(n1 + 1):N] == 0)*(bisR[l,]>0) + ww[, l] * (y[(n1 + 1):N] == 1)*((bisR[l,]-bisL[l,])>0))
      # tempa = 2
      tempb = eta + sum(bisT[l, ] * exp(xcov[1:n1, ] %*% beta+bsV[1:n1, ]%*%fcoef))+ sum(((bisR[l, ]) * (y[(n1 + 1):N] == 0) + (bisR[l, ]) * (y[(n1 + 1):N] == 1) + (bisL[l, ]) * (y[(n1 + 1):N] == 2)*U[(n1+1):N]) * exp(xcov[(n1 + 1):N, ] %*% beta+bsV[(n1 + 1):N, ]%*%fcoef))
      
      gamcoef[l] = rgamma(1, tempa, rate = tempb)
      
      
    }
    eta = rgamma(1, a_eta+K, rate = b_eta+sum(gamcoef))
    pargam[iter, ] = gamcoef
    pareta[iter] = eta
    ##sample beta
    xx=as.matrix(cbind(xcov,bsV))
    mu=c(rep(0,p),fprior)
    for (r in 1:p) {
      rho[r]<-arms(rho[r],rho_fun,indFunc=ind_fun_rho,1,r=r,rho=rho,n1=n1,N=N,xx=xx,mu=mu,te1=te1,te2=te2,te3=te3,sig_rho=sig_beta,coef_range_rho=coef_range_beta)
    }
    for (r in (p+1):(p+kf)){
      rho[r]<-arms(rho[r],rho_fun,indFunc=ind_fun_rho,1,r=r,rho=rho,n1=n1,N=N,xx=xx,mu=mu,te1=te1,te2=te2,te3=te3,sig_rho=sig_rho,coef_range_rho=coef_range_rho)
    }
    
    beta = as.matrix(rho[1:p],ncol=1)
    fcoef = rho[(p+1):(p+kf)]
    parbeta[iter,] = beta
    parfcoef[iter,] = fcoef
    parf[iter,] = bsVg%*%fcoef 
    
    
    
    lambdatT = t(gamcoef %*% bmsT)
    LambdatT = t(gamcoef %*% bisT)
    LambdatL = t(gamcoef %*% bisL)
    LambdatR = t(gamcoef %*% bisR)
    ##sample u
    u = array(rep(0, n1 * K), dim = c(n1, K))
    for (i in 1:n1) {
      u[i, ] = rmultinom(1, 1, gamcoef * t(bmsT[, i]))
    }
    ##sample alpha
    zz=as.matrix(cbind(zcov,bsW))
    mu1=c(rep(0,q),gprior)
    ## #for alpha
    for (i in 1:q) {
      theta[i] = arms(theta[i],theta_fun,indFunc=ind_fun_theta,1,i=i,theta=theta,U=U,mu1=mu1,zz=zz,sig_theta=sig_alpha,
                      coef_range_theta=coef_range_alpha)
    }
    
    for (i in (q+1):(q+kg)) {
      theta[i] = arms(theta[i],theta_fun,indFunc=ind_fun_theta,1,i=i,theta=theta,U=U,mu1=mu1,zz=zz,sig_theta=sig_theta,
                      coef_range_theta=coef_range_theta)
    }
    alpha = theta[1:q]
    gcoef = theta[(q+1):(q+kg)]
    paralpha[iter,] = alpha
    pargcoef[iter,] = gcoef
    parg[iter,] = bsWg%*%gcoef
    
    ##sample U cure indicator
    p_i = exp(zcov%*%alpha+bsW%*%gcoef)/(1+exp(zcov%*%alpha+bsW%*%gcoef))
    SL = exp(-rbind(LambdatT,LambdatL)*exp(xcov%*%beta+bsV%*%fcoef))
    # SL = exp(-(L^2)*exp(xcov%*%beta))
    pest = p_i*SL/(1-p_i+p_i*SL)
    U = ifelse(y==2, rbinom(N,1,pest), 1)
    
    parsurv0[iter, ] <- gamcoef %*% bisg
    parlambdatT[iter, ] = lambdatT
    parLambdatT[iter, ] = LambdatT
    parLambdatL[iter, ] = LambdatL
    parLambdatR[iter, ] = LambdatR
    
    iter = iter + 1
    if (iter%%100 == 0) 
      print(iter)
  }
  wbeta = as.matrix(parbeta[seq((burnin + thin), total, by = thin), ], ncol = p)
  walpha = as.matrix(paralpha[seq((burnin + thin), total, by = thin), ], ncol = q)
  wparsurv0 = as.matrix(parsurv0[seq((burnin + thin), total, by = thin), ], ncol = kgrids)
  wfcoef = as.matrix(parfcoef[seq((burnin+thin),total,by=thin),],ncol=kv)
  wf = as.matrix(parf[seq((burnin+thin),total,by=thin),],ncol=kve)
  wgcoef = as.matrix(pargcoef[seq((burnin+thin),total,by=thin),],ncol=kg)
  wg = as.matrix(parg[seq((burnin+thin),total,by=thin),],ncol=kgg)
  
  ebeta <- apply(wbeta, 2, mean)
  ealpha <- apply(walpha, 2, mean)
  efcoef = apply(wfcoef,2,mean)
  ef = apply(wf,2,mean);
  egcoef = apply(wgcoef,2,mean)
  eg = apply(wg,2,mean)
  S0_m <- apply(wparsurv0, 2, mean)
  ##save estimates
  est <- list(N = nrow(xcov), parbeta=parbeta,wbeta = wbeta, beta = ebeta, 
              paralpha=paralpha,walpha=walpha,alpha = ealpha,wparsurv0 = wparsurv0,
              S0_m = S0_m, grids = grids,pargam=pargam,fcoef=efcoef,
              gcoef=egcoef,wf=wf,ef=ef,wg=wg,eg=eg,Vgrid = Vgrid,Wgrid=Wgrid,U=U,bisg=bisg)
  est
}
 
  
  
  
  
  

