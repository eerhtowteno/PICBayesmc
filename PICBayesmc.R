rm(list=ls())
#############################################################################
SMC <- function (data,order, knots, df,grids,
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
  library(dlm)
  library(splines)
  library(icenReg)
  library(survival)
  Ispline <- function(x, order, knots) {
    k = order + 1
    m = length(knots)
    n = m - 2 + k
    t = c(rep(1, k) * knots[1], knots[2:(m - 1)], rep(1, 
                                                      k) * knots[m])
    yy1 = array(rep(0, (n + k - 1) * length(x)), dim = c(n + 
                                                           k - 1, length(x)))
    for (l in k:n) {
      yy1[l, ] = (x >= t[l] & x < t[l + 1])/(t[l + 1] - 
                                               t[l])
    }
    yytem1 = yy1
    for (ii in 1:order) {
      yytem2 = array(rep(0, (n + k - 1 - ii) * length(x)), 
                     dim = c(n + k - 1 - ii, length(x)))
      for (i in (k - ii):n) {
        yytem2[i, ] = (ii + 1) * ((x - t[i]) * yytem1[i, 
        ] + (t[i + ii + 1] - x) * yytem1[i + 1, ])/(t[i + 
                                                        ii + 1] - t[i])/ii
      }
      yytem1 = yytem2
    }
    index = rep(0, length(x))
    for (i in 1:length(x)) {
      index[i] = sum(t <= x[i])
    }
    yy = array(rep(0, (n - 1) * length(x)), dim = c(n - 1, 
                                                    length(x)))
    if (order == 1) {
      for (i in 2:n) {
        yy[i - 1, ] = (i < index - order + 1) + (i == 
                                                   index) * (t[i + order + 1] - t[i]) * yytem2[i, 
                                                   ]/(order + 1)
      }
    }
    else {
      for (j in 1:length(x)) {
        for (i in 2:n) {
          if (i < (index[j] - order + 1)) {
            yy[i - 1, j] = 1
          }
          else if ((i <= index[j]) && (i >= (index[j] - 
                                             order + 1))) {
            yy[i - 1, j] = (t[(i + order + 1):(index[j] + 
                                                 order + 1)] - t[i:index[j]]) %*% yytem2[i:index[j], 
                                                                                         j]/(order + 1)
          }
          else {
            yy[i - 1, j] = 0
          }
        }
      }
    }
    return(yy)
  }
  Mspline <- function(x, order, knots) {
    k1 = order
    m = length(knots)
    n1 = m - 2 + k1
    t1 = c(rep(1, k1) * knots[1], knots[2:(m - 1)], rep(1, 
                                                        k1) * knots[m])
    tem1 = array(rep(0, (n1 + k1 - 1) * length(x)), dim = c(n1 + 
                                                              k1 - 1, length(x)))
    for (l in k1:n1) {
      tem1[l, ] = (x >= t1[l] & x < t1[l + 1])/(t1[l + 
                                                     1] - t1[l])
    }
    if (order == 1) {
      mbases = tem1
    }
    else {
      mbases = tem1
      for (ii in 1:(order - 1)) {
        tem = array(rep(0, (n1 + k1 - 1 - ii) * length(x)), 
                    dim = c(n1 + k1 - 1 - ii, length(x)))
        for (i in (k1 - ii):n1) {
          tem[i, ] = (ii + 1) * ((x - t1[i]) * mbases[i, 
          ] + (t1[i + ii + 1] - x) * mbases[i + 1, 
          ])/(t1[i + ii + 1] - t1[i])/ii
        }
        mbases = tem
      }
    }
    return(mbases)
  }
  poissrndpositive <- function(lambda) {
    q = 200
    t = seq(0, q, 1)
    p = dpois(t, lambda)
    pp = cumsum(p[2:(q + 1)])/(1 - p[1])
    u = runif(1)
    while (u > pp[q]) {
      q = q + 1
      pp[q] = pp[q - 1] + dpois(q, lambda)/(1 - p[1])
    }
    ll = sum(u > pp) + 1
  }
  positivepoissonrnd<-function(lambda){ 
    samp = rpois(1, lambda)
    while (samp==0) {
      samp = rpois(1, lambda)
    }
    return(samp)
  }
  theta_fun <- function(x, i, theta, U, zz,mu1,sig_theta, coef_range_theta){
    theta[i] <- x
    mu = mu1[i]
    tt<- sum(zz%*%theta*U -log(1+exp(zz%*%theta)))-(x-mu)^2/sig_theta^2/2
    return(tt)
  }
  ind_fun_theta<- function(x, i, theta, U, zz,mu1,sig_theta, coef_range_theta){(x>-coef_range_theta)*(x<coef_range_theta)}
  rho_fun <- function(x,r,rho,n1,N,xx,mu,te1,te2,te3,sig_rho,coef_range_rho) 
  {
    rho[r]<-x
    mub = mu[r]
    tt<-sum(x*xx[1:n1, r] - te3 * exp(xx[1:n1,] %*% rho)) + sum(xx[(n1+1):N,r]*x*te1)-sum(exp(xx[(n1 + 1):N, ]%*%rho)*te2)-(x-mub)^2/sig_rho^2/2 # prior(beta)=N(0,sig0^2) 
    return(tt)     
  }
  ind_fun_rho <- function(x,r,rho,n1,N,xx,mu,te1,te2,te3,sig_rho,coef_range_rho)
  {(x>-coef_range_rho)*(x<coef_range_rho)}
  
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
  
  est <- list(N = nrow(xcov), parbeta=parbeta,wbeta = wbeta, beta = ebeta, 
              paralpha=paralpha,walpha=walpha,alpha = ealpha,wparsurv0 = wparsurv0,
              S0_m = S0_m, grids = grids,pargam=pargam,fcoef=efcoef,
              gcoef=egcoef,wf=wf,ef=ef,wg=wg,eg=eg,Vgrid = Vgrid,Wgrid=Wgrid,U=U,bisg=bisg)
  est
}
CPIC.simu<- function(n,alpha, beta,n1)
{
  #data generation
  library(dplyr)
  index <- 1:n 
  # Z = cbind(rbinom(n,1, 0.5),ifelse(index%%2==0,1,0))
  Z = cbind(rnorm(n,3,1),rbinom(n,1, 0.5))
  # Z = cbind(1,rbinom(n,1, 0.5),rbinom(n,1, 0.5),rbinom(n,1, 0.5),rbinom(n,1, 0.5))
  W <- runif(n,0,1)
  # W <- rnorm(n,0,1) 
  g <- sin(W*pi)
  # g <- W
  # g <- 1/(1+exp(-(W-0.5)*4))
  # g <- pnorm(W*2-3)/2+pnorm(W*2+3)/2
  # g <- pnorm(W*2-1)*0.6
  # g <- W
  # g <- 0
  cuindi<-function(alpha, g, n)
  {
    eta <- Z%*%alpha+g # uncured probability
    prob<-exp(eta)/(1+exp(eta));
    U <- rbinom(n, 1, prob) 
    re= list(U= U, eta =eta)
    return(re)
  }
  U1 <- cuindi(alpha[1,], g,n)$U; eta1 = cuindi(alpha[1,], g,n)$eta
  U2 <- cuindi(alpha[2,], g,n)$U; eta2 = cuindi(alpha[2,], g,n)$eta;
  mean(U1); mean(U2)
  
  # X <- cbind(rbinom(n,1,0.5),ifelse(index%%2==0,1,0))
  X <- cbind(rnorm(n,0,1),rbinom(n,1,0.5))
  # X <- cbind(rbinom(n,1, 0.5),rbinom(n,1, 0.5),rbinom(n,1, 0.5),rbinom(n,1, 0.5))
  V <- runif(n ,0, 1)
  # V <- rnorm(n ,0, 1)
  # V <- rtruncnorm(n, a=-2, b=2, mean = 0, sd = 1);
  f<- V^2
  # f <- sin(V*pi)
  # f <- log(V^V+0.5)-0.4
  # f <- V
  # f <- pnorm(V*2-3)/2+pnorm(V*2+3)/2
  # f <- 0
  
  
  y <- matrix(rep(0,n), nrow=n, ncol=1)
  L <- matrix(rep(0,n), nrow=n, ncol=1)
  R <- matrix(rep(0,n), nrow=n, ncol=1)
  C <-matrix(1.2, nrow = n, ncol = 1)     # length of study
  u <- runif(n, 0, 1)
  # True<- sqrt(-log(1-u)*exp(-X%*%beta-f))
  True<- sqrt(-0.5*log(1-u)*exp(-X%*%beta-f))
  # True<- exp(-log(1-u)*exp(-X%*%beta-f))-1
  # True<- sqrt(exp(-log(1-u)*exp(-X%*%beta-f))-1)
  # True<- -log(1-u)*exp(-X%*%beta-f)*0.5
  icProc<- function(True, C, U)
  {
    lp <-0 ; rp <-rexp(1,5)
    if (U==0) return(c(C, Inf))
    if (U==1)
    {
      if (True >= C)  return(c(C, Inf)) 
      if (True < C & True < rp) return(c(lp,rp))
      if (True < C & True > rp) 
      {
        repeat{ 
          lp <- rp ; rp <- rp+ runif(1,0,0.2)
          if(True>lp & True< rp ) {break}
        }
        return(c(lp, rp))
      }
    }
  }
  intends <-mapply(icProc, True = True, C=C, U=U1)
  y <- ifelse(intends[1,]==0,0,1) ;y <- ifelse(intends[2,]==Inf, 2, y)
  X1 <- data.frame(L = intends[1,], R = intends[2,],T=True,y = y,U=U1,X = X,V = V, Z = Z, W = W,eta=eta1)
  if(n1>0){
    IC=rep(1,n);X1=cbind(X1,IC)
    ind=sample(which(X1$U==1&X1$y==1),min(n1,sum(X1$U==1&X1$y==1)))
    X1$L[ind]=X1$T[ind];X1$R[ind]=X1$T[ind];
    X1$y[ind]=3;X1$IC[ind]=0}
  X1 <- X1 %>% arrange(IC)
  if(n1==0){
    X1 = X1
  }
  X1 = cbind(X1,IC)
  
  intends <-mapply(icProc, True = True, C=C, U=U2)
  y <- ifelse(intends[1,]==0,0,1) ;y <- ifelse(intends[2,]==Inf, 2, y)
  X2 <- data.frame(L = intends[1,], R = intends[2,],T=True,y = y,U=U2,X = X,V = V, Z = Z, W = W,eta=eta2)
  if(n1>0){
    IC=rep(1,n);X2=cbind(X2,IC)
    ind=sample(which(X2$U==1&X2$y==1),min(n1,sum(X2$U==1&X2$y==1)))
    X2$L[ind]=X2$T[ind];X2$R[ind]=X2$T[ind];
    X2$y[ind]=3;X2$IC[ind]=0}
  X2 <- X2 %>% arrange(IC)
  if(n1==0){
    X2 = X2
  }
  X2 = cbind(X2,IC)
  
  cr.t <- c(sum(X1$R==Inf)/n,sum(X2$R==Inf)/n)
  cr.cure<- c(sum(X1$U==0)/n,sum(X2$U==0)/n)
  
  return(list(X1 = X1, X2 = X2, cr.t = cr.t, cr.cure = cr.cure))
}


### Data generation
n <- 500 #sample size
n1 <- 0.1*n #exact number
alpha <- matrix(c(0.5,0.5,-0.5, -0.5), nrow = 2, byrow = TRUE) 
beta <- c(0.5,-0.5)
data1=CPIC.simu(n,alpha, beta,n1)

X1 <- data1$X1


fit <- SMC(X1,order = 2,knots = NULL, df=5,grids = seq(0, 3, length.out = 100),
              V.order=2,Vknots=NULL,V.df=5,Vgrid=seq(0,1,length.out = 50),
              W.order=2,Wknots=NULL,W.df=5,Wgrid=seq(0,1,length.out = 50),
              a_eta = 1, b_eta = 1, 
              coef_range_beta = 5,sig_beta = 5,coef_range_alpha = 5,sig_alpha = 5,
              coef_range_rho = 10,sig_rho = 5,coef_range_theta = 10,sig_theta =5,
              total = 10000, burnin = 5000, thin = 10)
  
  
  
  
  
  

