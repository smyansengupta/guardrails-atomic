import { clerkMiddleware, createRouteMatcher, currentUser } from '@clerk/nextjs/server';
import { NextResponse } from 'next/server';
import { logger } from '@/lib/utils/logger';

const isPublicRoute = createRouteMatcher([
  '/',
  '/sign-in(.*)',
  '/sign-up(.*)',
  '/api/validate',
  '/api/examples',
  '/api/generate-spec',
]);

export default clerkMiddleware(async (auth, request) => {

  logger.info('Incoming request', {
    method: request.method,
    path: request.nextUrl.pathname,
    // userId: user?.id,
  });

  if (!isPublicRoute(request)) {
    auth.protect();
  }

  return NextResponse.next();
});

export const config = {
  matcher: [
    '/((?!.+\.[\w]+$|_next).*)',
    '/',
    '/(api|trpc)(.*)',
  ],
};
